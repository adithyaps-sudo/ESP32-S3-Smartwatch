/*
 * ESP32-S3 Smartwatch - MPU6500 Version + BLE (NimBLE)
 * - 3 buttons
 * - 3 faces
 * - full-screen menu
 * - reduced screen flicker
 * - heart measurement only on Heart face
 * - MPU6500 direct register read
 * - improved filtered peak-based step counter
 * - WiFi + local Flask backend support
 * - AI Summary menu item
 * - BLE custom service for phone connection
 */

#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_ST7789.h>
#include <SPI.h>
#include "MAX30105.h"
#include "spo2_algorithm.h"
#include <math.h>
#include <WiFi.h>
#include <HTTPClient.h>
#include <ArduinoJson.h>
#include <NimBLEDevice.h>

// ========================================
// PIN DEFINITIONS
// ========================================

// ST7789 Display Pins
#define TFT_MOSI 12
#define TFT_SCLK 13
#define TFT_DC   10
#define TFT_RST  11
#define TFT_CS   9
#define TFT_BLK  8

// I2C Pins
#define I2C_SDA  2
#define I2C_SCL  1

// Buttons
#define BTN_LEFT    4
#define BTN_MIDDLE  5
#define BTN_RIGHT   6

// MPU6500
#define MPU_ADDR 0x68

// ========================================
// COLORS
// ========================================

#define COLOR_DARKGREY 0x52AA

// ========================================
// WIFI / BACKEND CONFIG
// ========================================

const char* WIFI_SSID = "YOUR_WIFI_NAME";
const char* WIFI_PASSWORD = "YOUR_PASSWORD";

const char* BACKEND_BASE_URL = "http://10.11.0.232:3000";
const char* BACKEND_TEST_URL = "http://10.11.0.232:3000/test";
const char* BACKEND_ASK_URL = "http://10.11.0.232:3000/ask";

// ========================================
// BLE CONFIG
// ========================================

static const char* BLE_DEVICE_NAME = "Smartwatch";

// Custom service/characteristics UUIDs
static const char* BLE_SERVICE_UUID      = "6f3d1000-4c55-4e7f-bb4a-7b6f10a0a001";
static const char* BLE_METRICS_CHAR_UUID = "6f3d1001-4c55-4e7f-bb4a-7b6f10a0a001";
static const char* BLE_COMMAND_CHAR_UUID = "6f3d1002-4c55-4e7f-bb4a-7b6f10a0a001";
static const char* BLE_STATUS_CHAR_UUID  = "6f3d1003-4c55-4e7f-bb4a-7b6f10a0a001";
static const char* BLE_SUMMARY_CHAR_UUID = "6f3d1004-4c55-4e7f-bb4a-7b6f10a0a001";

// ========================================
// HARDWARE INITIALIZATION
// ========================================

Adafruit_ST7789 tft = Adafruit_ST7789(&SPI, TFT_CS, TFT_DC, TFT_RST);
MAX30105 heartSensor;

// ========================================
// GLOBAL VARIABLES
// ========================================

// Heart rate variables
uint32_t irBuffer[100];
uint32_t redBuffer[100];
int32_t spo2 = 0;
int8_t validSPO2 = 0;
int32_t heartRate = 0;
int8_t validHeartRate = 0;
unsigned long lastHRUpdate = 0;
bool hrMeasuring = false;
bool heartSensorReady = false;
bool mpuReady = false;

// Step / motion variables
int stepCount = 0;
unsigned long lastStepTime = 0;
bool stepDetected = false;

bool isMoving = false;
unsigned long lastMovementTime = 0;
const unsigned long IDLE_TIMEOUT = 2000;

// Motion raw values
int16_t ax, ay, az, gx, gy, gz;
float accelMagnitude = 0.0;
float motionSignal = 0.0;
float filteredMotion = 0.0;
float previousFilteredMotion = 0.0;

// Step tuning
const float MOTION_ALPHA = 0.18;
const float STEP_PEAK_THRESHOLD = 0.10;
const unsigned long STEP_DEBOUNCE_TIME = 280;
const float MOVEMENT_THRESHOLD = 0.05;

// Simulated time variables
int hours = 12;
int minutes = 30;
int seconds = 0;
unsigned long lastTimeUpdate = 0;

// UI timing
unsigned long lastDynamicUpdate = 0;
const unsigned long DYNAMIC_UPDATE_INTERVAL = 200;

// WiFi / backend state
bool wifiConnected = false;
String backendAnswer = "";
unsigned long lastBackendCall = 0;

// BLE state
bool bleConnected = false;
bool bleMetricsDirty = true;
unsigned long lastBLEUpdate = 0;
const unsigned long BLE_UPDATE_INTERVAL = 1000;

String bleStatusText = "Advertising";

// ========================================
// UI STATE
// ========================================

enum UIMode {
  MODE_FACE,
  MODE_MENU,
  MODE_AI_RESULT
};

enum FaceType {
  FACE_CLOCK = 0,
  FACE_HEART = 1,
  FACE_ACTIVITY = 2
};

UIMode currentMode = MODE_FACE;
FaceType currentFace = FACE_CLOCK;
int menuIndex = 0;
bool screenDirty = true;

const char* menuItems[] = {
  "Clock Face",
  "Heart Tracker",
  "Activity Tracker",
  "AI Summary",
  "Back"
};
const int MENU_ITEMS_COUNT = 5;

// Cached last-drawn values to avoid unnecessary redraws
int lastShownHours = -1;
int lastShownMinutes = -1;
int lastShownSeconds = -1;
bool lastShownMoving = false;
int lastShownHeartRate = -999;
int lastShownSpO2 = -999;
bool lastShownValidHeartRate = false;
bool lastShownValidSpO2 = false;
bool lastShownHrMeasuring = false;
int lastShownStepCount = -1;
bool lastShownStepDetected = false;
bool lastShownBLEConnected = false;

// ========================================
// BUTTON STATE
// ========================================

struct Button {
  int pin;
  bool stableState;
  bool lastReading;
  unsigned long lastDebounceTime;
};

Button btnLeft   = { BTN_LEFT, HIGH, HIGH, 0 };
Button btnMiddle = { BTN_MIDDLE, HIGH, HIGH, 0 };
Button btnRight  = { BTN_RIGHT, HIGH, HIGH, 0 };

const unsigned long DEBOUNCE_DELAY = 40;
const unsigned long DOUBLE_CLICK_TIME = 350;

bool middleWaitingSecondClick = false;
unsigned long middleFirstClickTime = 0;

// ========================================
// BLE OBJECTS
// ========================================

NimBLEServer* bleServer = nullptr;
NimBLEService* bleService = nullptr;
NimBLECharacteristic* bleMetricsChar = nullptr;
NimBLECharacteristic* bleCommandChar = nullptr;
NimBLECharacteristic* bleStatusChar = nullptr;
NimBLECharacteristic* bleSummaryChar = nullptr;

// ========================================
// FUNCTION DECLARATIONS
// ========================================

void updateTime();
void readAccelerometer();
void detectSteps();
void detectMovement();
void measureHeartRate();

void updateButtons();
bool updateButton(Button &button);
void handleLeftPress();
void handleRightPress();
void handleMiddlePress();
void handlePendingMiddleSingleClick();

void navigateFaceLeft();
void navigateFaceRight();
void openMenu();
void closeMenu();
void menuUp();
void menuDown();
void selectMenuItem();
void goToClockFace();
void openAISummary();
void markScreenDirty();
void resetFaceCaches();

void drawCurrentScreen();
void drawClockFaceStatic();
void drawHeartFaceStatic();
void drawActivityFaceStatic();
void drawMenu();
void drawAIResultScreen();
void updateCurrentDynamicContent();
void updateClockFaceDynamic(bool force);
void updateHeartFaceDynamic(bool force);
void updateActivityFaceDynamic(bool force);

void drawCenteredText(const char* text, int y, uint16_t color, int textSize);
void drawHeader(const char* title, uint16_t color);
void drawFooterHint(const char* text, uint16_t color);

// MPU6500 helpers
void writeMPUReg(uint8_t reg, uint8_t value);
uint8_t readMPUReg(uint8_t reg);
void readMPUBytes(uint8_t reg, uint8_t count, uint8_t *dest);
bool initMPU6500();

// WiFi / backend helpers
void scanWiFiNetworks();
void connectToWiFi();
bool sendBackendTest();
bool askBackend(const String &question, const String &intent, const String &period);
void drawWiFiStatus();
void drawBackendAnswer(const String &text);

// BLE helpers
void initBLE();
void updateBLE();
void updateBLEMetrics(bool forceNotify = false);
void updateBLEStatus();
void notifySummaryOverBLE(const String &text);
void drawBLEStatus();
bool parseAndSetTime(const String &value);
void handleBLECommand(const String &command);

// ========================================
// BLE CALLBACKS
// ========================================

class SmartwatchServerCallbacks : public NimBLEServerCallbacks {
  void onConnect(NimBLEServer* pServer, NimBLEConnInfo& connInfo) override {
    bleConnected = true;
    bleStatusText = "Connected";
    bleMetricsDirty = true;
    Serial.println("BLE client connected");
    markScreenDirty();
  }

  void onDisconnect(NimBLEServer* pServer, NimBLEConnInfo& connInfo, int reason) override {
    bleConnected = false;
    bleStatusText = "Advertising";
    Serial.println("BLE client disconnected");

    NimBLEDevice::startAdvertising();
    markScreenDirty();
  }
};

class CommandCharacteristicCallbacks : public NimBLECharacteristicCallbacks {
  void onWrite(NimBLECharacteristic* pCharacteristic, NimBLEConnInfo& connInfo) override {
    std::string value = pCharacteristic->getValue();
    if (value.empty()) return;

    String command = String(value.c_str());
    command.trim();

    Serial.print("BLE command received: ");
    Serial.println(command);

    handleBLECommand(command);
  }
};

// ========================================
// MPU6500 FUNCTIONS
// ========================================

void writeMPUReg(uint8_t reg, uint8_t value) {
  Wire.beginTransmission(MPU_ADDR);
  Wire.write(reg);
  Wire.write(value);
  Wire.endTransmission();
}

uint8_t readMPUReg(uint8_t reg) {
  Wire.beginTransmission(MPU_ADDR);
  Wire.write(reg);
  Wire.endTransmission(false);
  Wire.requestFrom(MPU_ADDR, 1);

  if (Wire.available()) return Wire.read();
  return 0xFF;
}

void readMPUBytes(uint8_t reg, uint8_t count, uint8_t *dest) {
  Wire.beginTransmission(MPU_ADDR);
  Wire.write(reg);
  Wire.endTransmission(false);
  Wire.requestFrom(MPU_ADDR, count);

  uint8_t i = 0;
  while (Wire.available() && i < count) {
    dest[i++] = Wire.read();
  }
}

bool initMPU6500() {
  uint8_t whoami = readMPUReg(0x75);
  Serial.print("MPU WHO_AM_I: 0x");
  Serial.println(whoami, HEX);

  if (whoami != 0x70) {
    return false;
  }

  writeMPUReg(0x6B, 0x80);
  delay(100);

  writeMPUReg(0x6B, 0x01);
  delay(20);

  writeMPUReg(0x1A, 0x03);
  writeMPUReg(0x1B, 0x00);
  writeMPUReg(0x1C, 0x00);
  writeMPUReg(0x1D, 0x03);
  delay(20);

  return true;
}

// ========================================
// WIFI / BACKEND FUNCTIONS
// ========================================

void scanWiFiNetworks() {
  Serial.println("Scanning WiFi...");
  int n = WiFi.scanNetworks();

  if (n == 0) {
    Serial.println("No networks found");
    return;
  }

  Serial.print(n);
  Serial.println(" networks found:");

  for (int i = 0; i < n; i++) {
    Serial.print(i + 1);
    Serial.print(". SSID: ");
    Serial.print(WiFi.SSID(i));
    Serial.print(" | RSSI: ");
    Serial.print(WiFi.RSSI(i));
    Serial.print(" | Channel: ");
    Serial.print(WiFi.channel(i));
    Serial.print(" | Encryption: ");
    Serial.println(WiFi.encryptionType(i));
  }
}

void connectToWiFi() {
  Serial.println("================================");
  Serial.print("Connecting to SSID: ");
  Serial.println(WIFI_SSID);
  Serial.print("Password length: ");
  Serial.println(strlen(WIFI_PASSWORD));
  Serial.println("================================");

  wifiConnected = false;

  WiFi.mode(WIFI_OFF);
  delay(1000);

  WiFi.disconnect(true, true);
  delay(1000);

  WiFi.mode(WIFI_STA);
  WiFi.setSleep(false);
  WiFi.persistent(false);
  delay(500);

  WiFi.begin(WIFI_SSID, WIFI_PASSWORD);

  tft.fillScreen(ST77XX_BLACK);
  drawCenteredText("WiFi Connect", 70, ST77XX_CYAN, 2);
  drawCenteredText(WIFI_SSID, 105, ST77XX_WHITE, 2);
  drawCenteredText("Please wait...", 145, ST77XX_YELLOW, 2);

  unsigned long startAttempt = millis();
  const unsigned long timeoutMs = 25000;

  while (millis() - startAttempt < timeoutMs) {
    wl_status_t status = WiFi.status();

    // Serial.print("WiFi status: ");
    // Serial.println(status);

    if (status == WL_CONNECTED) {
      wifiConnected = true;

      Serial.println("WiFi connected!");
      Serial.print("IP: ");
      Serial.println(WiFi.localIP());

      tft.fillScreen(ST77XX_BLACK);
      drawCenteredText("WiFi Connected", 80, ST77XX_GREEN, 2);
      drawCenteredText(WiFi.localIP().toString().c_str(), 120, ST77XX_WHITE, 2);
      delay(1200);
      return;
    }

    delay(500);
  }

  wl_status_t status = WiFi.status();

  Serial.print("Final WiFi status: ");
  Serial.println(status);
  Serial.print("Tried SSID: ");
  Serial.println(WIFI_SSID);

  String reason = "Unknown";
  if (status == WL_NO_SSID_AVAIL) reason = "SSID not found";
  else if (status == WL_CONNECT_FAILED) reason = "Auth failed";
  else if (status == WL_CONNECTION_LOST) reason = "Connection lost";
  else if (status == WL_DISCONNECTED) reason = "Disconnected";
  else if (status == WL_IDLE_STATUS) reason = "Idle/timeout";

  Serial.print("WiFi failed: ");
  Serial.println(reason);

  tft.fillScreen(ST77XX_BLACK);
  drawCenteredText("WiFi Failed", 80, ST77XX_RED, 2);
  drawCenteredText(reason.c_str(), 120, ST77XX_WHITE, 2);
  delay(2000);
}

bool sendBackendTest() {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("WiFi not connected");
    wifiConnected = false;
    return false;
  }

  HTTPClient http;
  http.begin(BACKEND_TEST_URL);

  int httpCode = http.GET();
  Serial.print("GET /test code: ");
  Serial.println(httpCode);

  if (httpCode > 0) {
    String payload = http.getString();
    Serial.println("Response:");
    Serial.println(payload);

    StaticJsonDocument<512> doc;
    DeserializationError error = deserializeJson(doc, payload);

    if (!error) {
      bool ok = doc["ok"] | false;
      String answer = doc["answer"] | "";

      if (ok) {
        backendAnswer = answer;
        http.end();
        return true;
      }
    } else {
      Serial.print("JSON parse failed: ");
      Serial.println(error.c_str());
    }
  } else {
    Serial.print("HTTP GET failed: ");
    Serial.println(http.errorToString(httpCode));
  }

  http.end();
  return false;
}

bool askBackend(const String &question, const String &intent, const String &period) {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("WiFi not connected");
    wifiConnected = false;
    return false;
  }

  HTTPClient http;
  http.begin(BACKEND_ASK_URL);
  http.addHeader("Content-Type", "application/json");

  StaticJsonDocument<512> requestDoc;
  requestDoc["question"] = question;
  requestDoc["intent"] = intent;
  requestDoc["period"] = period;

  JsonObject metrics = requestDoc.createNestedObject("metrics");
  metrics["heart_rate"] = heartRate;
  metrics["spo2"] = spo2;
  metrics["steps"] = stepCount;
  metrics["moving"] = isMoving;
  metrics["valid_heart_rate"] = validHeartRate;
  metrics["valid_spo2"] = validSPO2;

  String requestBody;
  serializeJson(requestDoc, requestBody);

  Serial.println("POST /ask body:");
  Serial.println(requestBody);

  int httpCode = http.POST(requestBody);

  Serial.print("POST /ask code: ");
  Serial.println(httpCode);

  if (httpCode > 0) {
    String payload = http.getString();
    Serial.println("Response:");
    Serial.println(payload);

    StaticJsonDocument<1024> responseDoc;
    DeserializationError error = deserializeJson(responseDoc, payload);

    if (!error) {
      bool ok = responseDoc["ok"] | false;
      String answer = responseDoc["answer"] | "";

      if (ok) {
        backendAnswer = answer;
        http.end();
        return true;
      }
    } else {
      Serial.print("JSON parse failed: ");
      Serial.println(error.c_str());
    }
  } else {
    Serial.print("HTTP POST failed: ");
    Serial.println(http.errorToString(httpCode));
  }

  http.end();
  return false;
}

void drawWiFiStatus() {
  tft.fillRect(180, 38, 55, 16, ST77XX_BLACK);
  tft.setTextSize(1);
  tft.setCursor(182, 42);

  if (WiFi.status() == WL_CONNECTED) {
    tft.setTextColor(ST77XX_GREEN);
    tft.print("WiFi OK");
  } else {
    tft.setTextColor(ST77XX_RED);
    tft.print("No WiFi");
  }
}

void drawBackendAnswer(const String &text) {
  tft.fillRect(10, 206, 220, 12, ST77XX_BLACK);
  tft.setTextSize(1);
  tft.setTextColor(ST77XX_GREEN);
  tft.setCursor(10, 208);

  String shown = text;
  if (shown.length() > 34) {
    shown = shown.substring(0, 34);
  }

  tft.print(shown);
}

// ========================================
// BLE FUNCTIONS
// ========================================

void initBLE() {
  Serial.println("Initializing BLE...");

  NimBLEDevice::init(BLE_DEVICE_NAME);
  NimBLEDevice::setPower(ESP_PWR_LVL_P9);

  bleServer = NimBLEDevice::createServer();
  bleServer->setCallbacks(new SmartwatchServerCallbacks());

  bleService = bleServer->createService(BLE_SERVICE_UUID);

  bleMetricsChar = bleService->createCharacteristic(
    BLE_METRICS_CHAR_UUID,
    NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::NOTIFY
  );

  bleCommandChar = bleService->createCharacteristic(
    BLE_COMMAND_CHAR_UUID,
    NIMBLE_PROPERTY::WRITE | NIMBLE_PROPERTY::WRITE_NR
  );

  bleStatusChar = bleService->createCharacteristic(
    BLE_STATUS_CHAR_UUID,
    NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::NOTIFY
  );

  bleSummaryChar = bleService->createCharacteristic(
    BLE_SUMMARY_CHAR_UUID,
    NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::NOTIFY
  );

  bleCommandChar->setCallbacks(new CommandCharacteristicCallbacks());

  bleMetricsChar->setValue("HR=0;SPO2=0;STEPS=0;MOVING=0");
  bleStatusChar->setValue("Advertising");
  bleSummaryChar->setValue("No summary");

  bleService->start();

  NimBLEAdvertising* advertising = NimBLEDevice::getAdvertising();
  advertising->addServiceUUID(BLE_SERVICE_UUID);
  advertising->start();

  bleConnected = false;
  bleStatusText = "Advertising";

  Serial.println("BLE advertising started");
}

void updateBLEStatus() {
  StaticJsonDocument<256> doc;
  doc["ble_connected"] = bleConnected;
  doc["wifi_connected"] = (WiFi.status() == WL_CONNECTED);
  doc["mode"] = (int)currentMode;
  doc["face"] = (int)currentFace;
  doc["hr_measuring"] = hrMeasuring;

  String payload;
  serializeJson(doc, payload);

  bleStatusChar->setValue(payload.c_str());
  if (bleConnected) {
    bleStatusChar->notify();
  }
}

void updateBLEMetrics(bool forceNotify) {
  StaticJsonDocument<256> doc;
  doc["heart_rate"] = heartRate;
  doc["valid_heart_rate"] = validHeartRate;
  doc["spo2"] = spo2;
  doc["valid_spo2"] = validSPO2;
  doc["steps"] = stepCount;
  doc["moving"] = isMoving;
  doc["hours"] = hours;
  doc["minutes"] = minutes;
  doc["seconds"] = seconds;

  String payload;
  serializeJson(doc, payload);

  bleMetricsChar->setValue(payload.c_str());

  if (bleConnected && (forceNotify || bleMetricsDirty)) {
    bleMetricsChar->notify();
  }

  bleMetricsDirty = false;
}

void notifySummaryOverBLE(const String &text) {
  bleSummaryChar->setValue(text.c_str());
  if (bleConnected) {
    bleSummaryChar->notify();
  }
}

bool parseAndSetTime(const String &value) {
  int h, m, s;
  if (sscanf(value.c_str(), "%d:%d:%d", &h, &m, &s) == 3) {
    if (h >= 0 && h < 24 && m >= 0 && m < 60 && s >= 0 && s < 60) {
      hours = h;
      minutes = m;
      seconds = s;
      lastTimeUpdate = millis();
      resetFaceCaches();
      markScreenDirty();
      bleMetricsDirty = true;
      Serial.println("Time updated from BLE");
      return true;
    }
  }
  return false;
}

void handleBLECommand(const String &command) {
  if (command.startsWith("SET_TIME:")) {
    String value = command.substring(String("SET_TIME:").length());
    bool ok = parseAndSetTime(value);
    notifySummaryOverBLE(ok ? "Time updated" : "Invalid time format");
    return;
  }

  if (command == "FACE:CLOCK") {
    currentFace = FACE_CLOCK;
    currentMode = MODE_FACE;
    resetFaceCaches();
    markScreenDirty();
    bleMetricsDirty = true;
    notifySummaryOverBLE("Face set to Clock");
    return;
  }

  if (command == "FACE:HEART") {
    currentFace = FACE_HEART;
    currentMode = MODE_FACE;
    resetFaceCaches();
    markScreenDirty();
    bleMetricsDirty = true;
    notifySummaryOverBLE("Face set to Heart");
    return;
  }

  if (command == "FACE:ACTIVITY") {
    currentFace = FACE_ACTIVITY;
    currentMode = MODE_FACE;
    resetFaceCaches();
    markScreenDirty();
    bleMetricsDirty = true;
    notifySummaryOverBLE("Face set to Activity");
    return;
  }

  if (command == "OPEN_MENU") {
    openMenu();
    notifySummaryOverBLE("Menu opened");
    return;
  }

  if (command == "CLOCK") {
    goToClockFace();
    notifySummaryOverBLE("Clock opened");
    return;
  }

  if (command == "REQUEST_SUMMARY") {
    backendAnswer = "Requesting summary...";
    notifySummaryOverBLE(backendAnswer);

    bool ok = askBackend(
      "How is my heart rate today?",
      "heart_summary",
      "today"
    );

    if (ok) {
      currentMode = MODE_AI_RESULT;
      markScreenDirty();
      notifySummaryOverBLE(backendAnswer);
    } else {
      backendAnswer = "Backend request failed";
      currentMode = MODE_AI_RESULT;
      markScreenDirty();
      notifySummaryOverBLE(backendAnswer);
    }

    return;
  }

  notifySummaryOverBLE("Unknown command");
}

void updateBLE() {
  if (millis() - lastBLEUpdate >= BLE_UPDATE_INTERVAL) {
    lastBLEUpdate = millis();
    updateBLEMetrics(false);
    updateBLEStatus();
  }
}

void drawBLEStatus() {
  tft.fillRect(120, 38, 56, 16, ST77XX_BLACK);
  tft.setTextSize(1);
  tft.setCursor(122, 42);

  if (bleConnected) {
    tft.setTextColor(ST77XX_GREEN);
    tft.print("BLE OK");
  } else {
    tft.setTextColor(ST77XX_YELLOW);
    tft.print("BLE ADV");
  }
}

// ========================================
// SETUP
// ========================================

void setup() {
  Serial.begin(115200);
  delay(1000);

  Serial.println("\n========================================");
  Serial.println("ESP32-S3 Smartwatch - MPU6500 + BLE");
  Serial.println("========================================\n");

  pinMode(BTN_LEFT, INPUT_PULLUP);
  pinMode(BTN_MIDDLE, INPUT_PULLUP);
  pinMode(BTN_RIGHT, INPUT_PULLUP);

  Serial.println("Initializing I2C...");
  Wire.begin(I2C_SDA, I2C_SCL);
  Wire.setClock(100000);
  delay(200);
  Serial.println("I2C OK");

  Serial.println("Initializing MPU6500...");
  mpuReady = initMPU6500();
  if (mpuReady) {
    Serial.println("MPU6500 OK");
  } else {
    Serial.println("MPU6500 FAILED - will continue anyway");
  }

  Serial.println("Initializing MAX30102...");
  if (heartSensor.begin(Wire, I2C_SPEED_FAST)) {
    Serial.println("MAX30102 OK");
    heartSensor.setup(60, 4, 2, 100, 411, 4096);
    heartSensorReady = true;
  } else {
    Serial.println("MAX30102 FAILED - will continue anyway");
    heartSensorReady = false;
  }

  Serial.println("Initializing ST7789 Display...");

  pinMode(TFT_CS, OUTPUT);
  digitalWrite(TFT_CS, LOW);

  pinMode(TFT_BLK, OUTPUT);
  digitalWrite(TFT_BLK, HIGH);

  SPI.begin(TFT_SCLK, -1, TFT_MOSI, TFT_CS);
  delay(100);

  tft.init(240, 240, SPI_MODE3);
  tft.setRotation(2);
  tft.fillScreen(ST77XX_BLACK);
  Serial.println("Display OK");

  drawCenteredText("Smartwatch", 95, ST77XX_CYAN, 3);
  drawCenteredText("Starting...", 135, ST77XX_WHITE, 2);
  delay(1200);

  initBLE();

  // scanWiFiNetworks();
  connectToWiFi();

  if (wifiConnected) {
    bool testOk = sendBackendTest();

    tft.fillScreen(ST77XX_BLACK);
    if (testOk) {
      drawCenteredText("Backend OK", 80, ST77XX_GREEN, 2);
      drawCenteredText(backendAnswer.c_str(), 120, ST77XX_WHITE, 2);
      notifySummaryOverBLE(backendAnswer);
    } else {
      drawCenteredText("Backend Failed", 80, ST77XX_RED, 2);
      drawCenteredText("Check Flask server", 120, ST77XX_WHITE, 2);
      notifySummaryOverBLE("Backend Failed");
    }
    delay(1500);
  }

  markScreenDirty();
  drawCurrentScreen();

  updateBLEMetrics(true);
  updateBLEStatus();

  Serial.println("\nSmartwatch Ready!\n");
}

// ========================================
// MAIN LOOP
// ========================================

void loop() {
  updateTime();

  if (mpuReady) {
    readAccelerometer();
    detectSteps();
    detectMovement();
  }

  if (currentMode == MODE_FACE && currentFace == FACE_HEART) {
    measureHeartRate();
  }

  updateButtons();
  handlePendingMiddleSingleClick();

  if (screenDirty) {
    drawCurrentScreen();
  }

  if (millis() - lastDynamicUpdate >= DYNAMIC_UPDATE_INTERVAL) {
    lastDynamicUpdate = millis();
    updateCurrentDynamicContent();
  }

  updateBLE();

  delay(10);
}

// ========================================
// TIME FUNCTIONS
// ========================================

void updateTime() {
  if (millis() - lastTimeUpdate >= 1000) {
    lastTimeUpdate = millis();
    seconds++;
    bleMetricsDirty = true;

    if (seconds >= 60) {
      seconds = 0;
      minutes++;

      if (minutes >= 60) {
        minutes = 0;
        hours++;

        if (hours >= 24) {
          hours = 0;
        }
      }
    }
  }
}

// ========================================
// ACCELEROMETER FUNCTIONS
// ========================================

void readAccelerometer() {
  uint8_t data[14];
  readMPUBytes(0x3B, 14, data);

  ax = (int16_t)((data[0] << 8) | data[1]);
  ay = (int16_t)((data[2] << 8) | data[3]);
  az = (int16_t)((data[4] << 8) | data[5]);
  gx = (int16_t)((data[8] << 8) | data[9]);
  gy = (int16_t)((data[10] << 8) | data[11]);
  gz = (int16_t)((data[12] << 8) | data[13]);

  float ax_g = ax / 16384.0;
  float ay_g = ay / 16384.0;
  float az_g = az / 16384.0;

  accelMagnitude = sqrt(ax_g * ax_g + ay_g * ay_g + az_g * az_g);

  motionSignal = fabs(accelMagnitude - 1.0);

  filteredMotion = (MOTION_ALPHA * motionSignal) +
                   ((1.0 - MOTION_ALPHA) * previousFilteredMotion);
}

void detectSteps() {
  stepDetected = false;
  unsigned long now = millis();

  bool risingEdge =
    (filteredMotion > STEP_PEAK_THRESHOLD) &&
    (previousFilteredMotion <= STEP_PEAK_THRESHOLD);

  if (risingEdge && (now - lastStepTime) > STEP_DEBOUNCE_TIME) {
    stepCount++;
    lastStepTime = now;
    stepDetected = true;
    bleMetricsDirty = true;

    Serial.print("Step detected! Total: ");
    Serial.println(stepCount);
  }

  previousFilteredMotion = filteredMotion;
}

void detectMovement() {
  bool oldMoving = isMoving;

  if (filteredMotion > MOVEMENT_THRESHOLD) {
    isMoving = true;
    lastMovementTime = millis();
  } else {
    if (millis() - lastMovementTime > IDLE_TIMEOUT) {
      isMoving = false;
    }
  }

  if (oldMoving != isMoving) {
    bleMetricsDirty = true;
  }
}

// ========================================
// HEART RATE FUNCTIONS
// ========================================

void measureHeartRate() {
  if (!heartSensorReady) return;

  if (millis() - lastHRUpdate >= 3000) {
    lastHRUpdate = millis();
    hrMeasuring = true;
    bleMetricsDirty = true;

    Serial.println("Measuring heart rate...");

    for (byte i = 0; i < 100; i++) {
      while (heartSensor.available() == false) {
        heartSensor.check();
      }

      redBuffer[i] = heartSensor.getRed();
      irBuffer[i] = heartSensor.getIR();
      heartSensor.nextSample();
    }

    maxim_heart_rate_and_oxygen_saturation(
      irBuffer, 100, redBuffer,
      &spo2, &validSPO2,
      &heartRate, &validHeartRate
    );

    if (validHeartRate) {
      Serial.print("Heart Rate: ");
      Serial.print(heartRate);
      Serial.println(" bpm");
    } else {
      Serial.println("Heart Rate: Invalid (no finger detected)");
    }

    hrMeasuring = false;
    bleMetricsDirty = true;
    updateBLEMetrics(true);
  }
}

// ========================================
// BUTTON FUNCTIONS
// ========================================

bool updateButton(Button &button) {
  bool reading = digitalRead(button.pin);

  if (reading != button.lastReading) {
    button.lastDebounceTime = millis();
  }

  if ((millis() - button.lastDebounceTime) > DEBOUNCE_DELAY) {
    if (reading != button.stableState) {
      button.stableState = reading;

      if (button.stableState == LOW) {
        button.lastReading = reading;
        return true;
      }
    }
  }

  button.lastReading = reading;
  return false;
}

void updateButtons() {
  if (updateButton(btnLeft)) {
    handleLeftPress();
  }

  if (updateButton(btnRight)) {
    handleRightPress();
  }

  if (updateButton(btnMiddle)) {
    handleMiddlePress();
  }
}

void handleLeftPress() {
  Serial.println("LEFT press");

  if (currentMode == MODE_FACE) {
    navigateFaceLeft();
  } else if (currentMode == MODE_MENU) {
    menuUp();
  }
}

void handleRightPress() {
  Serial.println("RIGHT press");

  if (currentMode == MODE_FACE) {
    navigateFaceRight();
  } else if (currentMode == MODE_MENU) {
    menuDown();
  }
}

void handleMiddlePress() {
  Serial.println("MIDDLE press");

  unsigned long now = millis();

  if (middleWaitingSecondClick &&
      (now - middleFirstClickTime) <= DOUBLE_CLICK_TIME) {

    middleWaitingSecondClick = false;
    Serial.println("MIDDLE double click");

    if (currentMode == MODE_FACE) {
      goToClockFace();
    } else if (currentMode == MODE_MENU) {
      closeMenu();
    } else if (currentMode == MODE_AI_RESULT) {
      goToClockFace();
    }
  } else {
    middleWaitingSecondClick = true;
    middleFirstClickTime = now;
  }
}

void handlePendingMiddleSingleClick() {
  if (middleWaitingSecondClick &&
      (millis() - middleFirstClickTime) > DOUBLE_CLICK_TIME) {

    middleWaitingSecondClick = false;
    Serial.println("MIDDLE single click");

    if (currentMode == MODE_FACE) {
      openMenu();
    } else if (currentMode == MODE_MENU) {
      selectMenuItem();
    } else if (currentMode == MODE_AI_RESULT) {
      openMenu();
    }
  }
}

// ========================================
// NAVIGATION FUNCTIONS
// ========================================

void markScreenDirty() {
  screenDirty = true;
}

void resetFaceCaches() {
  lastShownHours = -1;
  lastShownMinutes = -1;
  lastShownSeconds = -1;
  lastShownMoving = !isMoving;
  lastShownHeartRate = -999;
  lastShownSpO2 = -999;
  lastShownValidHeartRate = !validHeartRate;
  lastShownValidSpO2 = !validSPO2;
  lastShownHrMeasuring = !hrMeasuring;
  lastShownStepCount = -1;
  lastShownStepDetected = !stepDetected;
  lastShownBLEConnected = !bleConnected;
}

void navigateFaceLeft() {
  if (currentFace == FACE_CLOCK) currentFace = FACE_ACTIVITY;
  else currentFace = (FaceType)((int)currentFace - 1);

  markScreenDirty();
  resetFaceCaches();
  bleMetricsDirty = true;
}

void navigateFaceRight() {
  if (currentFace == FACE_ACTIVITY) currentFace = FACE_CLOCK;
  else currentFace = (FaceType)((int)currentFace + 1);

  markScreenDirty();
  resetFaceCaches();
  bleMetricsDirty = true;
}

void openMenu() {
  currentMode = MODE_MENU;

  if (currentFace == FACE_CLOCK) menuIndex = 0;
  else if (currentFace == FACE_HEART) menuIndex = 1;
  else menuIndex = 2;

  markScreenDirty();
  bleMetricsDirty = true;
}

void closeMenu() {
  currentMode = MODE_FACE;
  markScreenDirty();
  resetFaceCaches();
  bleMetricsDirty = true;
}

void menuUp() {
  menuIndex--;
  if (menuIndex < 0) menuIndex = MENU_ITEMS_COUNT - 1;
  markScreenDirty();
}

void menuDown() {
  menuIndex++;
  if (menuIndex >= MENU_ITEMS_COUNT) menuIndex = 0;
  markScreenDirty();
}

void openAISummary() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("AI Summary", ST77XX_CYAN);
  drawCenteredText("Requesting...", 100, ST77XX_YELLOW, 2);
  drawFooterHint("M:menu  Mx2:clock", ST77XX_CYAN);

  bool ok = askBackend(
    "How is my heart rate today?",
    "heart_summary",
    "today"
  );

  if (ok) {
    currentMode = MODE_AI_RESULT;
    notifySummaryOverBLE(backendAnswer);
  } else {
    backendAnswer = "Backend request failed";
    currentMode = MODE_AI_RESULT;
    notifySummaryOverBLE(backendAnswer);
  }

  markScreenDirty();
  bleMetricsDirty = true;
}

void selectMenuItem() {
  switch (menuIndex) {
    case 0:
      currentFace = FACE_CLOCK;
      currentMode = MODE_FACE;
      break;
    case 1:
      currentFace = FACE_HEART;
      currentMode = MODE_FACE;
      break;
    case 2:
      currentFace = FACE_ACTIVITY;
      currentMode = MODE_FACE;
      break;
    case 3:
      openAISummary();
      return;
    case 4:
      currentMode = MODE_FACE;
      break;
  }

  markScreenDirty();
  resetFaceCaches();
  bleMetricsDirty = true;
}

void goToClockFace() {
  currentFace = FACE_CLOCK;
  currentMode = MODE_FACE;
  markScreenDirty();
  resetFaceCaches();
  bleMetricsDirty = true;
}

// ========================================
// DISPLAY FUNCTIONS
// ========================================

void drawCurrentScreen() {
  screenDirty = false;

  if (currentMode == MODE_MENU) {
    drawMenu();
    return;
  }

  if (currentMode == MODE_AI_RESULT) {
    drawAIResultScreen();
    return;
  }

  if (currentFace == FACE_CLOCK) {
    drawClockFaceStatic();
    updateClockFaceDynamic(true);
  } else if (currentFace == FACE_HEART) {
    drawHeartFaceStatic();
    updateHeartFaceDynamic(true);
  } else if (currentFace == FACE_ACTIVITY) {
    drawActivityFaceStatic();
    updateActivityFaceDynamic(true);
  }
}

void updateCurrentDynamicContent() {
  if (currentMode != MODE_FACE) return;

  if (currentFace == FACE_CLOCK) {
    updateClockFaceDynamic(false);
  } else if (currentFace == FACE_HEART) {
    updateHeartFaceDynamic(false);
  } else if (currentFace == FACE_ACTIVITY) {
    updateActivityFaceDynamic(false);
  }
}

void drawHeader(const char* title, uint16_t color) {
  tft.fillRect(0, 0, 240, 36, color);
  tft.setTextSize(2);
  tft.setTextColor(ST77XX_WHITE);
  tft.setCursor(10, 10);
  tft.print(title);
}

void drawFooterHint(const char* text, uint16_t color) {
  tft.fillRect(0, 220, 240, 20, ST77XX_BLACK);
  tft.drawLine(0, 219, 240, 219, color);
  tft.setTextSize(1);
  tft.setTextColor(color);
  tft.setCursor(8, 226);
  tft.print(text);
}

void drawCenteredText(const char* text, int y, uint16_t color, int textSize) {
  int16_t x1, y1;
  uint16_t w, h;
  tft.setTextSize(textSize);
  tft.getTextBounds((char*)text, 0, y, &x1, &y1, &w, &h);
  int x = (240 - w) / 2;
  tft.setCursor(x, y);
  tft.setTextColor(color);
  tft.print(text);
}

void drawClockFaceStatic() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("Clock", ST77XX_BLUE);
  drawFooterHint("L/R faces  M:menu  Mx2:clock", ST77XX_BLUE);
}

void updateClockFaceDynamic(bool force) {
  if (force || hours != lastShownHours || minutes != lastShownMinutes) {
    char timeBuffer[6];
    sprintf(timeBuffer, "%02d:%02d", hours, minutes);
    tft.fillRect(20, 70, 200, 50, ST77XX_BLACK);
    drawCenteredText(timeBuffer, 80, ST77XX_WHITE, 5);
    lastShownHours = hours;
    lastShownMinutes = minutes;
  }

  if (force || seconds != lastShownSeconds) {
    char secBuffer[4];
    sprintf(secBuffer, ":%02d", seconds);
    tft.fillRect(70, 135, 100, 28, ST77XX_BLACK);
    drawCenteredText(secBuffer, 145, ST77XX_CYAN, 3);
    lastShownSeconds = seconds;
  }

  if (force || isMoving != lastShownMoving) {
    tft.fillRect(40, 178, 160, 26, ST77XX_BLACK);
    if (isMoving) {
      drawCenteredText("MOVING", 185, ST77XX_YELLOW, 2);
    } else {
      drawCenteredText("IDLE", 185, ST77XX_RED, 2);
    }
    lastShownMoving = isMoving;
  }

  drawBLEStatus();
  drawWiFiStatus();
}

void drawHeartFaceStatic() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("Heart Tracker", ST77XX_RED);

  tft.drawRoundRect(60, 170, 120, 36, 6, ST77XX_CYAN);

  drawFooterHint("L/R faces  M:menu  Mx2:clock", ST77XX_RED);
}

void updateHeartFaceDynamic(bool force) {
  if (force || hrMeasuring != lastShownHrMeasuring) {
    tft.fillRect(20, 44, 200, 24, ST77XX_BLACK);
    if (hrMeasuring) {
      drawCenteredText("MEASURING...", 48, ST77XX_YELLOW, 2);
    } else {
      drawCenteredText("HEART RATE", 48, ST77XX_RED, 2);
    }
    lastShownHrMeasuring = hrMeasuring;
  }

  if (force || heartRate != lastShownHeartRate || validHeartRate != lastShownValidHeartRate) {
    tft.fillRect(20, 80, 200, 60, ST77XX_BLACK);
    if (validHeartRate && heartRate > 0) {
      char hrBuffer[8];
      sprintf(hrBuffer, "%ld", heartRate);
      drawCenteredText(hrBuffer, 85, ST77XX_WHITE, 5);
    } else {
      drawCenteredText("--", 85, ST77XX_WHITE, 5);
    }
    lastShownHeartRate = heartRate;
    lastShownValidHeartRate = validHeartRate;
  }

  if (force) {
    tft.fillRect(80, 140, 80, 24, ST77XX_BLACK);
    drawCenteredText("bpm", 145, ST77XX_WHITE, 2);
  }

  if (force || spo2 != lastShownSpO2 || validSPO2 != lastShownValidSpO2) {
    tft.fillRect(72, 180, 96, 28, ST77XX_BLACK);
    tft.setTextSize(2);
    tft.setTextColor(ST77XX_CYAN);
    tft.setCursor(72, 180);
    tft.print("SpO2:");
    tft.setCursor(92, 196);

    if (validSPO2 && spo2 > 0) {
      tft.print(spo2);
      tft.print("%");
    } else {
      tft.print("--");
    }

    lastShownSpO2 = spo2;
    lastShownValidSpO2 = validSPO2;
  }

  drawBLEStatus();
  drawWiFiStatus();
}

void drawActivityFaceStatic() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("Activity", ST77XX_GREEN);

  drawCenteredText("STEPS", 45, ST77XX_GREEN, 2);
  drawCenteredText("STATUS", 145, ST77XX_CYAN, 2);

  tft.drawCircle(215, 55, 8, COLOR_DARKGREY);

  drawFooterHint("L/R faces  M:menu  Mx2:clock", ST77XX_GREEN);
}

void updateActivityFaceDynamic(bool force) {
  if (force || stepCount != lastShownStepCount) {
    char stepBuffer[12];
    sprintf(stepBuffer, "%d", stepCount);
    tft.fillRect(20, 78, 180, 60, ST77XX_BLACK);
    drawCenteredText(stepBuffer, 78, ST77XX_WHITE, 5);
    lastShownStepCount = stepCount;
  }

  if (force || isMoving != lastShownMoving) {
    tft.fillRect(40, 170, 160, 26, ST77XX_BLACK);
    if (isMoving) {
      drawCenteredText("MOVING", 175, ST77XX_YELLOW, 2);
    } else {
      drawCenteredText("IDLE", 175, ST77XX_RED, 2);
    }
    lastShownMoving = isMoving;
  }

  if (force || stepDetected != lastShownStepDetected) {
    if (stepDetected) {
      tft.fillCircle(215, 55, 8, ST77XX_GREEN);
    } else {
      tft.fillCircle(215, 55, 8, ST77XX_BLACK);
      tft.drawCircle(215, 55, 8, COLOR_DARKGREY);
    }
    lastShownStepDetected = stepDetected;
  }

  drawBLEStatus();
  drawWiFiStatus();
}

void drawAIResultScreen() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("AI Summary", ST77XX_CYAN);
  drawBLEStatus();
  drawWiFiStatus();

  tft.setTextColor(ST77XX_WHITE);
  tft.setTextSize(2);
  tft.setCursor(12, 60);
  tft.print("Result:");

  tft.drawRoundRect(10, 90, 220, 90, 8, ST77XX_CYAN);

  tft.setTextSize(2);
  tft.setTextColor(ST77XX_GREEN);

  String line1 = backendAnswer;
  String line2 = "";
  String line3 = "";

  if (line1.length() > 22) {
    int split1 = line1.lastIndexOf(' ', 22);
    if (split1 <= 0) split1 = 22;
    line2 = line1.substring(split1 + 1);
    line1 = line1.substring(0, split1);
  }

  if (line2.length() > 22) {
    int split2 = line2.lastIndexOf(' ', 22);
    if (split2 <= 0) split2 = 22;
    line3 = line2.substring(split2 + 1);
    line2 = line2.substring(0, split2);
  }

  tft.setCursor(20, 105);
  tft.print(line1);

  if (line2.length() > 0) {
    tft.setCursor(20, 130);
    tft.print(line2);
  }

  if (line3.length() > 0) {
    tft.setCursor(20, 155);
    tft.print(line3);
  }

  drawFooterHint("M:menu  Mx2:clock", ST77XX_CYAN);
}

void drawMenu() {
  tft.fillScreen(ST77XX_BLACK);
  drawHeader("Menu", ST77XX_MAGENTA);
  tft.drawLine(0, 36, 240, 36, ST77XX_WHITE);

  for (int i = 0; i < MENU_ITEMS_COUNT; i++) {
    int y = 55 + i * 32;

    if (i == menuIndex) {
      tft.fillRoundRect(20, y - 4, 200, 28, 6, ST77XX_YELLOW);
      tft.setTextColor(ST77XX_BLACK);
    } else {
      tft.drawRoundRect(20, y - 4, 200, 28, 6, COLOR_DARKGREY);
      tft.setTextColor(ST77XX_WHITE);
    }

    tft.setTextSize(2);
    tft.setCursor(35, y);
    tft.print(menuItems[i]);
  }

  drawFooterHint("L:up  R:down  M:select  Mx2:back", ST77XX_MAGENTA);
}