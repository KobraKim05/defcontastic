#include "configuration.h"
#if !MESHTASTIC_EXCLUDE_GPS
#include "GPS.h"
#endif
#include "MeshRadio.h"
#include "MeshService.h"
#include "NodeDB.h"
#include "PowerFSM.h"
#include "PowerMon.h"
#include "ReliableRouter.h"
#include "airtime.h"
#include "buzz.h"

#include "error.h"
#include "power.h"
// #include "debug.h"
#include "FSCommon.h"
#include "RTC.h"
#include "SPILock.h"
#include "concurrency/OSThread.h"
#include "concurrency/Periodic.h"
#include "detect/ScanI2C.h"

#if !MESHTASTIC_EXCLUDE_I2C
#include "detect/ScanI2CTwoWire.h"
#include <Wire.h>
#endif
#include "detect/axpDebug.h"
#include "detect/einkScan.h"
#include "graphics/RAKled.h"
#include "graphics/Screen.h"
#include "main.h"
#include "mesh/generated/meshtastic/config.pb.h"
#include "modules/Modules.h"
#include "shutdown.h"
#include "sleep.h"
#include "target_specific.h"
#include <memory>
#include <utility>
// #include <driver/rtc_io.h>

#ifdef ARCH_ESP32
#if !MESHTASTIC_EXCLUDE_WEBSERVER
#include "mesh/http/WebServer.h"
#endif
#if !MESHTASTIC_EXCLUDE_BLUETOOTH
#include "nimble/NimbleBluetooth.h"
NimbleBluetooth *nimbleBluetooth = nullptr;
#endif
#endif

#if HAS_WIFI
#include "mesh/api/WiFiServerAPI.h"
#include "mesh/wifi/WiFiAPClient.h"
#endif

#if !MESHTASTIC_EXCLUDE_MQTT
#include "mqtt/MQTT.h"
#endif

#include "LLCC68Interface.h"
#include "LR1110Interface.h"
#include "LR1120Interface.h"
#include "RF95Interface.h"
#include "SX1262Interface.h"
#include "SX1268Interface.h"
#include "SX1280Interface.h"
#include "detect/LoRaRadioType.h"

#if HAS_BUTTON || defined(ARCH_PORTDUINO)
#include "ButtonThread.h"
#endif

#include "PowerFSMThread.h"

#if !defined(ARCH_PORTDUINO) && !defined(ARCH_STM32WL) && !MESHTASTIC_EXCLUDE_ENVIRONMENTAL_SENSOR
#include "AccelerometerThread.h"
AccelerometerThread *accelerometerThread = nullptr;
#endif

using namespace concurrency;

// We always create a screen object, but we only init it if we find the hardware
graphics::Screen *screen = nullptr;

// Global power status
meshtastic::PowerStatus *powerStatus = new meshtastic::PowerStatus();

// Global GPS status
meshtastic::GPSStatus *gpsStatus = new meshtastic::GPSStatus();

// Global Node status
meshtastic::NodeStatus *nodeStatus = new meshtastic::NodeStatus();

// Scan for I2C Devices

/// The I2C address of our display (if found)
ScanI2C::DeviceAddress screen_found = ScanI2C::ADDRESS_NONE;

// The I2C address of the cardkb or RAK14004 (if found)
ScanI2C::DeviceAddress cardkb_found = ScanI2C::ADDRESS_NONE;
// 0x02 for RAK14004, 0x00 for cardkb, 0x10 for T-Deck
uint8_t kb_model;

// The I2C address of the RTC Module (if found)
ScanI2C::DeviceAddress rtc_found = ScanI2C::ADDRESS_NONE;
// The I2C address of the Accelerometer (if found)
ScanI2C::DeviceAddress accelerometer_found = ScanI2C::ADDRESS_NONE;
// The I2C address of the RGB LED (if found)
ScanI2C::FoundDevice rgb_found = ScanI2C::FoundDevice(ScanI2C::DeviceType::NONE, ScanI2C::ADDRESS_NONE);

#if !defined(ARCH_PORTDUINO) && !defined(ARCH_STM32WL)
ATECCX08A atecc;
#endif

// Global LoRa radio type
LoRaRadioType radioType = NO_RADIO;

bool isVibrating = false;

bool eink_found = true;

uint32_t serialSinceMsec;
bool pauseBluetoothLogging = false;

bool pmu_found;

#if !MESHTASTIC_EXCLUDE_I2C
// Array map of sensor types with i2c address and wire as we'll find in the i2c scan
std::pair<uint8_t, TwoWire *> nodeTelemetrySensorsMap[_meshtastic_TelemetrySensorType_MAX + 1] = {};
#endif

Router *router = NULL; // Users of router don't care what sort of subclass implements that API

const char *getDeviceName()
{
    uint8_t dmac[6];

    getMacAddr(dmac);

    // Meshtastic_ab3c or Shortname_abcd
    static char name[20];
    snprintf(name, sizeof(name), "%02x%02x", dmac[4], dmac[5]);
    // if the shortname exists and is NOT the new default of ab3c, use it for BLE name.
    if (strcmp(owner.short_name, name) != 0) {
        snprintf(name, sizeof(name), "%s_%02x%02x", owner.short_name, dmac[4], dmac[5]);
    } else {
        snprintf(name, sizeof(name), "Meshtastic_%02x%02x", dmac[4], dmac[5]);
    }
    return name;
}

static int32_t ledBlinker()
{
    // Still set up the blinking (heartbeat) interval but skip code path below, so LED will blink if
    // config.device.led_heartbeat_disabled is changed
    if (config.device.led_heartbeat_disabled)
        return 1000;

    static bool ledOn;
    ledOn ^= 1;

    setLed(ledOn);

    // have a very sparse duty cycle of LED being on, unless charging, then blink 0.5Hz square wave rate to indicate that
    return powerStatus->getIsCharging() ? 1000 : (ledOn ? 1 : 1000);
}

uint32_t timeLastPowered = 0;

static Periodic *ledPeriodic;
static OSThread *powerFSMthread;

RadioInterface *rIf = NULL;

/**
 * Some platforms (nrf52) might provide an alterate version that suppresses calling delay from sleep.
 */
__attribute__((weak, noinline)) bool loopCanSleep()
{
    return true;
}

/**
 * Print info as a structured log message (for automated log processing)
 */
void printInfo()
{
    LOG_INFO("S:B:%d,%s\n", HW_VENDOR, optstr(APP_VERSION));
}

void setup()
{
    concurrency::hasBeenSetup = true;
#if ARCH_PORTDUINO
    SPISettings spiSettings(settingsMap[spiSpeed], MSBFIRST, SPI_MODE0);
#else
    SPISettings spiSettings(4000000, MSBFIRST, SPI_MODE0);
#endif

    meshtastic_Config_DisplayConfig_OledType screen_model =
        meshtastic_Config_DisplayConfig_OledType::meshtastic_Config_DisplayConfig_OledType_OLED_AUTO;
    OLEDDISPLAY_GEOMETRY screen_geometry = GEOMETRY_128_64;

#ifdef DEBUG_PORT
    consoleInit(); // Set serial baud rate and init our mesh console
#endif
    powerMonInit();

    serialSinceMsec = millis();

    LOG_INFO("\n\n//\\ E S H T /\\ S T / C\n\n");

    initDeepSleep();

#if defined(VEXT_ENABLE)
    pinMode(VEXT_ENABLE, OUTPUT);
    digitalWrite(VEXT_ENABLE, 0); // turn on the display power
#endif

#ifdef RESET_OLED
    pinMode(RESET_OLED, OUTPUT);
    digitalWrite(RESET_OLED, 1);
#endif

#ifdef BUTTON_PIN
#ifdef ARCH_ESP32

    // If the button is connected to GPIO 12, don't enable the ability to use
    // meshtasticAdmin on the device.
    pinMode(config.device.button_gpio ? config.device.button_gpio : BUTTON_PIN, INPUT);

#endif
#endif

    OSThread::setup();

    ledPeriodic = new Periodic("Blink", ledBlinker);

    fsInit();

#if !MESHTASTIC_EXCLUDE_I2C
#if defined(I2C_SDA1) && !defined(ARCH_RP2040)
    Wire1.begin(I2C_SDA1, I2C_SCL1);
#endif
#endif

#if defined(I2C_SDA) && !defined(ARCH_RP2040)
    Wire.begin(I2C_SDA, I2C_SCL);
#endif

    // Currently only the tbeam has a PMU
    // PMU initialization needs to be placed before i2c scanning
    power = new Power();
    power->setStatusHandler(powerStatus);
    powerStatus->observe(&power->newStatus);
    power->setup(); // Must be after status handler is installed, so that handler gets notified of the initial configuration

    // TODO: Initialize I2C devices
    auto i2cScanner = std::unique_ptr<ScanI2CTwoWire>(new ScanI2CTwoWire());

    Wire.begin(I2C_SDA, I2C_SCL);
    i2cScanner->scanPort(ScanI2C::I2CPort::WIRE);

    // Don't init display if we are waking headless due to a timer event
    if (wakeCause == ESP_SLEEP_WAKEUP_TIMER) {
        LOG_DEBUG("suppress screen wake because this is a headless timer wakeup");
        i2cScanner->setSuppressScreen();
    }

    auto screenInfo = i2cScanner->firstScreen();
    screen_found = screenInfo.type != ScanI2C::DeviceType::NONE ? screenInfo.address : ScanI2C::ADDRESS_NONE;

    if (screen_found.port != ScanI2C::I2CPort::NO_I2C) {
        switch (screenInfo.type) {
        case ScanI2C::DeviceType::SCREEN_SH1106:
            screen_model = meshtastic_Config_DisplayConfig_OledType::meshtastic_Config_DisplayConfig_OledType_OLED_SH1106;
            break;
        case ScanI2C::DeviceType::SCREEN_SSD1306:
            screen_model = meshtastic_Config_DisplayConfig_OledType::meshtastic_Config_DisplayConfig_OledType_OLED_SSD1306;
            break;
        case ScanI2C::DeviceType::SCREEN_ST7567:
        case ScanI2C::DeviceType::SCREEN_UNKNOWN:
        default:
            screen_model = meshtastic_Config_DisplayConfig_OledType::meshtastic_Config_DisplayConfig_OledType_OLED_AUTO;
        }
    }

    auto rtc_info = i2cScanner->firstRTC();
    rtc_found = rtc_info.type != ScanI2C::DeviceType::NONE ? rtc_info.address : rtc_found;

    pmu_found = i2cScanner->exists(ScanI2C::DeviceType::PMU_AXP192_AXP2101);

    i2cScanner.reset();

    // LED init

#ifdef LED_PIN
    pinMode(LED_PIN, OUTPUT);
    digitalWrite(LED_PIN, 1 ^ LED_INVERTED); // turn on for now
#endif

    // Hello
    printInfo();

#ifdef ARCH_ESP32
    esp32Setup();
#endif

    // We do this as early as possible because this loads preferences from flash
    // but we need to do this after main cpu init (esp32setup), because we need the random seed set
    nodeDB = new NodeDB;

    // If we're taking on the repeater role, use flood router and turn off 3V3_S rail because peripherals are not needed
    if (config.device.role == meshtastic_Config_DeviceConfig_Role_REPEATER) {
        router = new FloodingRouter();
#ifdef PIN_3V3_EN
        digitalWrite(PIN_3V3_EN, LOW);
#endif
    } else
        router = new ReliableRouter();

#if HAS_BUTTON || defined(ARCH_PORTDUINO)
    // Buttons. Moved here cause we need NodeDB to be initialized
    buttonThread = new ButtonThread();
#endif

    playStartMelody();

    // fixed screen override?
    if (config.display.oled != meshtastic_Config_DisplayConfig_OledType_OLED_AUTO)
        screen_model = config.display.oled;

    // Init our SPI controller (must be before screen and lora)
    initSPI();
    // ESP32
    SPI.begin(LORA_SCK, LORA_MISO, LORA_MOSI, LORA_CS);
    LOG_DEBUG("SPI.begin(SCK=%d, MISO=%d, MOSI=%d, NSS=%d)\n", LORA_SCK, LORA_MISO, LORA_MOSI, LORA_CS);
    SPI.setFrequency(4000000);

    // Initialize the screen first so we can show the logo while we start up everything else.
    screen = new graphics::Screen(screen_found, screen_model, screen_geometry);

    // setup TZ prior to time actions.
    if (*config.device.tzdef) {
        setenv("TZ", config.device.tzdef, 1);
    } else {
        setenv("TZ", "GMT0", 1);
    }
    tzset();
    LOG_DEBUG("Set Timezone to %s\n", getenv("TZ"));

    readFromRTC(); // read the main CPU RTC at first (in case we can't get GPS time)

#if !MESHTASTIC_EXCLUDE_GPS
    // If we're taking on the repeater role, ignore GPS
    if (HAS_GPS) {
        if (config.device.role != meshtastic_Config_DeviceConfig_Role_REPEATER &&
            config.position.gps_mode != meshtastic_Config_PositionConfig_GpsMode_NOT_PRESENT) {
            gps = GPS::createGps();
            if (gps) {
                gpsStatus->observe(&gps->newStatus);
            } else {
                LOG_DEBUG("Running without GPS.\n");
            }
        }
    }
#endif

    nodeStatus->observe(&nodeDB->newStatus);

    service = new MeshService();
    service->init();

    // Now that the mesh service is created, create any modules
    setupModules();

#ifdef LED_PIN
    // Turn LED off after boot, if heartbeat by config
    if (config.device.led_heartbeat_disabled)
        digitalWrite(LED_PIN, LOW ^ LED_INVERTED);
#endif

#if !MESHTASTIC_EXCLUDE_I2C
// Don't call screen setup until after nodedb is setup (because we need
// the current region name)
    if (screen_found.port != ScanI2C::I2CPort::NO_I2C)
        screen->setup();
#endif

    screen->print("Started...\n");

    LockingArduinoHal *RadioLibHAL = new LockingArduinoHal(SPI, spiSettings);

    // radio init MUST BE AFTER service.init, so we have our radio config settings (from nodedb init)
#if defined(USE_SX1262) && !defined(ARCH_PORTDUINO)
    if (!rIf) {
        rIf = new SX1262Interface(RadioLibHAL, SX126X_CS, SX126X_DIO1, SX126X_RESET, SX126X_BUSY);
        if (!rIf->init()) {
            LOG_WARN("Failed to find SX1262 radio\n");
            delete rIf;
            rIf = NULL;
        } else {
            LOG_INFO("SX1262 Radio init succeeded, using SX1262 radio\n");
            radioType = SX1262_RADIO;
        }
    }
#endif

    // check if the radio chip matches the selected region

    if ((config.lora.region == meshtastic_Config_LoRaConfig_RegionCode_LORA_24) && (!rIf->wideLora())) {
        LOG_WARN("Radio chip does not support 2.4GHz LoRa. Reverting to unset.\n");
        config.lora.region = meshtastic_Config_LoRaConfig_RegionCode_UNSET;
        nodeDB->saveToDisk(SEGMENT_CONFIG);
        if (!rIf->reconfigure()) {
            LOG_WARN("Reconfigure failed, rebooting\n");
            screen->startAlert("Rebooting...");
            rebootAtMsec = millis() + 5000;
        }
    }

#if !MESHTASTIC_EXCLUDE_MQTT
    mqttInit();
#endif

#ifndef ARCH_PORTDUINO

        // Initialize Wifi
#if HAS_WIFI
    initWifi();
#endif
#endif

#if defined(ARCH_ESP32) && !MESHTASTIC_EXCLUDE_WEBSERVER
    // Start web server thread.
    webServerThread = new WebServerThread();
#endif

    // Start airtime logger thread.
    airTime = new AirTime();

    if (!rIf)
        RECORD_CRITICALERROR(meshtastic_CriticalErrorCode_NO_RADIO);
    else {
        router->addInterface(rIf);

        // Log bit rate to debug output
        LOG_DEBUG("LoRA bitrate = %f bytes / sec\n", (float(meshtastic_Constants_DATA_PAYLOAD_LEN) /
                                                      (float(rIf->getPacketTime(meshtastic_Constants_DATA_PAYLOAD_LEN)))) *
                                                         1000);
    }

    // This must be _after_ service.init because we need our preferences loaded from flash to have proper timeout values
    PowerFSM_setup(); // we will transition to ON in a couple of seconds, FIXME, only do this for cold boots, not waking from SDS
    powerFSMthread = new PowerFSMThread();
    setCPUFast(false); // 80MHz is fine for our slow peripherals
}

uint32_t rebootAtMsec;   // If not zero we will reboot at this time (used to reboot shortly after the update completes)
uint32_t shutdownAtMsec; // If not zero we will shutdown at this time (used to shutdown from python or mobile client)

// If a thread does something that might need for it to be rescheduled ASAP it can set this flag
// This will suppress the current delay and instead try to run ASAP.
bool runASAP;

extern meshtastic_DeviceMetadata getDeviceMetadata()
{
    meshtastic_DeviceMetadata deviceMetadata;
    strncpy(deviceMetadata.firmware_version, optstr(APP_VERSION), sizeof(deviceMetadata.firmware_version));
    deviceMetadata.device_state_version = DEVICESTATE_CUR_VER;
    deviceMetadata.canShutdown = pmu_found || HAS_CPU_SHUTDOWN;
    deviceMetadata.hasBluetooth = HAS_BLUETOOTH;
    deviceMetadata.hasWifi = HAS_WIFI;
    deviceMetadata.hasEthernet = HAS_ETHERNET;
    deviceMetadata.role = config.device.role;
    deviceMetadata.position_flags = config.position.position_flags;
    deviceMetadata.hw_model = HW_VENDOR;
    deviceMetadata.hasRemoteHardware = moduleConfig.remote_hardware.enabled;
    return deviceMetadata;
}

void loop()
{
    runASAP = false;

    // axpDebugOutput.loop();

    // heap_caps_check_integrity_all(true); // FIXME - disable this expensive check

#ifdef ARCH_ESP32
    esp32Loop();
#endif
    powerCommandsCheck();

    // For debugging
    // if (rIf) ((RadioLibInterface *)rIf)->isActivelyReceiving();

    // TODO: This should go into a thread handled by FreeRTOS.
    // handleWebResponse();

    service->loop();

    long delayMsec = mainController.runOrDelay();

    /* if (mainController.nextThread && delayMsec)
        LOG_DEBUG("Next %s in %ld\n", mainController.nextThread->ThreadName.c_str(),
                  mainController.nextThread->tillRun(millis())); */

    // We want to sleep as long as possible here - because it saves power
    if (!runASAP && loopCanSleep()) {
        // if(delayMsec > 100) LOG_DEBUG("sleeping %ld\n", delayMsec);
        mainDelay.delay(delayMsec);
    }
    // if (didWake) LOG_DEBUG("wake!\n");
}
