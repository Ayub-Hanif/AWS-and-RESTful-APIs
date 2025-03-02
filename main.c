// Group Name: Raiyan Sazid, Mohammad Ayub Hanif Saleh

//*****************************************************************************
//
// Copyright (C) 2014 Texas Instruments Incorporated - http://www.ti.com/
//
//
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//
//    Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
//    Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the
//    distribution.
//
//    Neither the name of Texas Instruments Incorporated nor the names of
//    its contributors may be used to endorse or promote products derived
//    from this software without specific prior written permission.
//
//  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
//  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
//  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
//  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
//  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
//  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
//  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
//  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
//  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//*****************************************************************************


//*****************************************************************************
// Application Name     - SPI Demo
// Application Overview - The demo application focuses on showing the required
//                        initialization sequence to enable the CC3200 SPI
//                        module in full duplex 4-wire master and slave mode(s).
//*****************************************************************************


//*****************************************************************************
//! \addtogroup SPI_Demo
//! @{
//*****************************************************************************

// Standard includes
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

// Driverlib includes
#include "hw_nvic.h"
#include "hw_types.h"
#include "hw_memmap.h"
#include "hw_common_reg.h"
#include "hw_ints.h"
#include "spi.h"
#include "rom.h"
#include "rom_map.h"
#include "utils.h"
#include "prcm.h"
#include "uart.h"
#include "interrupt.h"
#include "gpio.h"
#include "systick.h"

// Common interface includes
#include "uart_if.h"
#include "pinmux.h"
#include "i2c_if.h"

// Adafruit libraries
#include "oled/Adafruit_SSD1351.h"
#include "oled/Adafruit_GFX.h"
#include "oled/oled_test.h"
#include "oled/glcdfont.h"

// Timer Libraries
#include "timer.h"
#include "timer_if.h"
#include "gpio_if.h"
#include <time.h>

#include <stdio.h>

// Simplelink includes
#include "simplelink.h"

//Driverlib includes
#include "hw_types.h"
#include "hw_ints.h"
#include "rom.h"
#include "rom_map.h"
#include "interrupt.h"
#include "prcm.h"
#include "utils.h"
#include "uart.h"

//Common interface includes
#include "pinmux.h"
#include "gpio_if.h"
#include "common.h"
#include "uart_if.h"

// Custom includes
#include "utils/network_utils.h"

//*****************************************************************************
//
//! \addtogroup ssl
//! @{
//*****************************************************************************

//*****************************************************************************
// Application Master/Slave mode selector macro
// MASTER_MODE = 1 : Application in master mode
// MASTER_MODE = 0 : Application in slave mode
//*****************************************************************************
#define MASTER_MODE      1

#define SPI_IF_BIT_RATE  16000000
#define TR_BUFF_SIZE     100

#define OLED_SPI_TX_DMA_CHANNEL    0x04

#define MASTER_MSG       "This is CC3200 SPI Master Application\n\r"
#define SLAVE_MSG        "This is CC3200 SPI Slave Application\n\r"

// Color definitions
#define BLACK           0x0000
#define BLUE            0x001F
#define RED             0xF800
#define GREEN           0x07E0
#define CYAN            0x07FF
#define MAGENTA         0xF81F
#define YELLOW          0xFFE0
#define WHITE           0xFFFF
#define PINK            0xFAFA

const char *TEXT_COLOR_PALET[] = {
                                  WHITE,
                                  BLUE,
                                  RED,
                                  GREEN,
                                  CYAN
};

// Number definitions
#define ONE              0xbe689740
#define TWO              0xbe423dc0
#define THREE            0xbe621dc0
#define FOUR             0xbe740bc0
#define FIVE             0xbe443bc0
#define SIX              0xbe641bc0
#define SEVEN            0xbe788740
#define EIGHT            0xbe748b40
#define NINE             0xbe7c8340
#define ZERO             0xbe4837c0
#define LAST             0xbe5827c0
#define MUTE             0xbe7807c0
#define VOLUME_INCREASE  0xbe4c33c0
#define VOLUME_DECREASE  0xbe6c13c0

// TIMER CONFIGURATION
#define TIMER_END_PERIOD 1000

// UART CONFIGURATION
#define UART_START_CMD "x"
#define UART_START_CMD_SIZE 0
#define UART_SIGNAL_DELAY 500

//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************

#if defined(ccs)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

// The CC3200's fixed clock frequency = 80 MHz
#define SYSCLKFREQ 80000000ULL

// Convert ticks to microseconds
#define TICKS_TO_US(ticks) \
    ((((ticks) / SYSCLKFREQ) * 1000000ULL) + \
     ((((ticks) % SYSCLKFREQ) * 1000000ULL) / SYSCLKFREQ))

// macro to convert microseconds back to ticks
#define US_TO_TICKS(us) ((SYSCLKFREQ / 1000000ULL) * (us))

// SysTick reload value set to 40ms
#define SYSTICK_RELOAD_VAL 3200000UL

volatile int systick_cnt = 0;
extern void (* const g_pfnVectors[])(void);

volatile uint64_t transmission_buffer[64];
volatile int tb_idx = 0;

volatile unsigned char text_buffer[64];
volatile int text_idx = 0;

volatile unsigned char recv_buffer[64];
volatile int recv_buffer_reset = 0;
volatile int recv_idx = 0;


// Globals used by the timer interrupt handler.
static volatile unsigned long g_ulSysTickValue;
static volatile unsigned long g_ulBase;
static volatile unsigned long g_ulRefBase;
static volatile unsigned long g_ulRefTimerInts = 0;
static volatile unsigned long g_ulIntClearVector;
unsigned long g_ulTimerInts;

//*****************************************************************************
//                 GLOBAL VARIABLES -- End
//*****************************************************************************

// Some helpful struct
struct IRDecoderValues {
    int sameButtonCount;
    int logButtonCount;
    unsigned long previousButton;
    char letter;
    char prevLetter;
    int timerStarter;
    int colorPalet;
};

volatile static struct IRDecoderValues DecoderVal = {0, 0, '?', '?', '?', 0, 0};

//*****************************************************************************
// Board Initialization & Configuration
//*****************************************************************************

static inline void SysTickReset(void) {
    HWREG(NVIC_ST_CURRENT) = 1;  // any write clears it
    systick_cnt = 0;
}

// Sleep for specified milli-seconds
void sleep(unsigned long time) {
    time *= 1000;
    volatile unsigned long delay;
    for (delay = 0; delay < time; delay++);
}

// Compute a wrap-aware difference between two SysTick counts
static inline uint64_t WrapAwareDiff(uint64_t start, uint64_t end) {
    // If no wrap has occurred:
    if (start >= end) {
        return (start - end);
    }
    // If wrap occurred:
    else {
        return (start + (SYSTICK_RELOAD_VAL - end));
    }
}

void sendUARTStart() {
    int i;
    for (i = 0; i < UART_START_CMD_SIZE; i++) {
        UARTCharPut(UARTA1_BASE, UART_START_CMD[i % UART_START_CMD_SIZE]);
        UtilsDelay(UART_SIGNAL_DELAY);
    }
}

/******************************************************************************
 * Decode IR pulses from 'transmission_buffer' into an unsigned long "value".
 * This logic depends on your IR remote's pulse timings and thresholds.
 ******************************************************************************/
unsigned long Decode_IR(uint64_t *buffer, int size) {
    if (size < 32) {
        // Not enough pulses or partial reading
        return 0;
    }

    unsigned long value = 0;
    int i, start_idx = 0;
    for (i = 0; i < size; i++) {
        // Convert ticks to microseconds
        unsigned long pulse_us = (unsigned long)(buffer[i] / 80);

        // If we see a huge gap, that often indicates the "start of a new sequence".
        if (pulse_us > 4000) {
            start_idx = 0;
            continue;
        }

        // example threshold ~1100 us for distinguishing '0' from '1'
        if (pulse_us > 1100) {
            value |= (1UL << (size - (start_idx)));
        }
        start_idx++;
    }

    //UART_PRINT("Decoded value: 0x%08lx\n\r", value);
    return value;
}

/******************************************************************************
 * Interprets the decoded IR "value" into the multi-tap logic.
 * If user presses the same button repeatedly, we cycle among letters.
 ******************************************************************************/
static void Processing_DecodedIR(unsigned long value) {
    char number = 0;

    // If MUTE was pressed, treat it like a "backspace".
    if (value == MUTE) {
        text_idx--;
        if (text_idx < 0) {
            text_idx = 0;
        }
        text_buffer[text_idx] = '\0';
        DecoderVal.previousButton = '\0';
        DecoderVal.sameButtonCount = 0;
        return;
    }

    if (DecoderVal.previousButton == value) {
        // same button pressed again => multi-tap cycle
        DecoderVal.sameButtonCount++;
        DecoderVal.logButtonCount = DecoderVal.sameButtonCount;
    } else {
        DecoderVal.sameButtonCount = 0;
    }

    switch(value) {
        case VOLUME_INCREASE:
            DecoderVal.colorPalet++;
            DecoderVal.sameButtonCount = DecoderVal.logButtonCount;
            break;
        case VOLUME_DECREASE:
            DecoderVal.colorPalet--;
            DecoderVal.sameButtonCount = DecoderVal.logButtonCount;
            break;
        case ONE:
            DecoderVal.letter = "1"[DecoderVal.sameButtonCount % 1];
            break;
        case TWO:
            number = '2';
            DecoderVal.letter = "ABC2"[DecoderVal.sameButtonCount % 4];
            break;
        case THREE:
            number = '3';
            DecoderVal.letter = "DEF3"[DecoderVal.sameButtonCount % 4];
            break;
        case FOUR:
            number = '4';
            DecoderVal.letter = "GHI4"[DecoderVal.sameButtonCount % 4];
            break;
        case FIVE:
            number = '5';
            DecoderVal.letter = "JKL5"[DecoderVal.sameButtonCount % 5];
            break;
        case SIX:
            number = '6';
            DecoderVal.letter = "MNO6"[DecoderVal.sameButtonCount % 4];
            break;
        case SEVEN:
            number = '7';
            DecoderVal.letter = "PQRS7"[DecoderVal.sameButtonCount % 5];
            break;
        case EIGHT:
            number = '8';
            DecoderVal.letter = "TUV8"[DecoderVal.sameButtonCount % 4];
            break;
        case NINE:
            number = '9';
            DecoderVal.letter = "WXYZ9"[DecoderVal.sameButtonCount % 5];
            break;
        case ZERO:
            number = '0';
            DecoderVal.letter = "0 "[DecoderVal.sameButtonCount % 2];
            break;
        case LAST:
            // Using 'LAST' as an Enter or "Send" => newline
            number = 'L';
            DecoderVal.letter = '\n';
            break;
        default:
            // If it's an unknown code, do nothing.
            DecoderVal.sameButtonCount = DecoderVal.logButtonCount;
            return;
    }

    // If we switched to a new button from the old button, that finishes the old letter
    if (DecoderVal.previousButton != value && text_buffer[text_idx] != '\0') {
        text_idx++;
        DecoderVal.sameButtonCount = 0;
    }

    DecoderVal.previousButton = value;
    text_buffer[text_idx] = DecoderVal.letter;

    // Let the "single press" timer start
    DecoderVal.timerStarter = 1;
}

/******************************************************************************
 * ISR: IR Receiver (GPIO) Handler
 ******************************************************************************/
static void GPIOA3IntHandler(void) {
    static int currState = 0;
    static uint64_t prevTime = 0;
    unsigned long ulStatus;

    ulStatus = MAP_GPIOIntStatus(IR_GPIO_PORT, true);
    MAP_GPIOIntClear(IR_GPIO_PORT, ulStatus);

    IntMasterDisable();
    if (ulStatus & IR_GPIO_PIN) {
        currState = MAP_GPIOPinRead(IR_GPIO_PORT, IR_GPIO_PIN);

        // If we are just now starting a new IR transmission
        if (tb_idx == 0) {
            Timer_IF_InterruptClear(g_ulBase);
            MAP_SysTickEnable();
            tb_idx = 1;
        }

        if (currState != 0) {
            prevTime = SysTickValueGet();
        } else {
            uint64_t currTime = SysTickValueGet();
            uint64_t elapsed = WrapAwareDiff(prevTime, currTime);
            transmission_buffer[tb_idx] = elapsed;
            tb_idx++;
        }
    }
    IntMasterEnable();
}

/******************************************************************************
 * ISR: SysTick Handler
 * Fires after ~40ms if no more IR pulses are seen.
 ******************************************************************************/
static void SysTickHandler(void) {
    MAP_SysTickDisable(); // done counting after 40ms
    IntMasterDisable();

    if (tb_idx > 0) {
        unsigned long decodedValue = Decode_IR((uint64_t *)transmission_buffer, tb_idx);
        Processing_DecodedIR(decodedValue);
    }
    tb_idx = 0;

    IntMasterEnable();

    if (DecoderVal.timerStarter) {
        Timer_IF_Start(g_ulBase, TIMER_A, TIMER_END_PERIOD);
    }
}

/******************************************************************************
 * ISR: Timer Handler
 * Once the user stops multi-tapping (1 second), we finalize that letter.
 ******************************************************************************/
static void SysTimerHandler(void) {
    Timer_IF_InterruptClear(g_ulBase);
    Timer_IF_Stop(g_ulBase, TIMER_A);
    MAP_SysTickDisable();

    text_idx++; // finalize the partial letter

    DecoderVal.sameButtonCount = 0;
    DecoderVal.logButtonCount = 0;
    DecoderVal.letter = '?';
    DecoderVal.previousButton = 0;
    DecoderVal.timerStarter = 0;
}

/******************************************************************************
 * ISR: UART1 Handler (receives text from other device, if used)
 ******************************************************************************/
static void UARTIntHandler(void) {
    unsigned char recvChar;
    unsigned long ulStatus;

    UARTIntDisable(UARTA1_BASE, UART_INT_RX);

    recv_idx = 0;
    while (UARTCharsAvail(UARTA1_BASE)) {
        recvChar = UARTCharGet(UARTA1_BASE);
        recv_buffer[recv_idx++] = recvChar;
        UtilsDelay(UART_SIGNAL_DELAY);
    }

    if (recv_idx < UART_START_CMD_SIZE) {
        recv_buffer[0] = '\0';
        recv_idx = 0;
    }

    int i;
    for (i = 0; i < UART_START_CMD_SIZE; i++) {
        if (UART_START_CMD[i] != recv_buffer[i]) {
            break;
        }
    }

    if (i != UART_START_CMD_SIZE) {
       recv_buffer[0] = '\0';
       recv_idx = 0;
    }

    recv_buffer[recv_idx] = '\0';
    recv_buffer_reset = 1;

    UARTIntClear(UARTA1_BASE, UART_INT_RX);
    UARTIntEnable(UARTA1_BASE, UART_INT_RX);
}

static int aws_post_message(const char *msg, int sockID);

//********************* OLED DISPLAY FUNCTIONS *********************************\\
//******************************************************************************\\

void DisplaySenderText(int lRetVal) {
    static int prevIndex = 0;
    static int inPlaceTextCount = 0;
    int newLines = 0;
    int lineIdx = 0;
    int i;
    int lineHeight = 80;



    for (i = 0; i < prevIndex; i++) {
        if (text_buffer[i] == '\n') {
            newLines++;
            lineIdx = 0;
        } else {
            lineIdx++;
        }
    }



    if (prevIndex < text_idx) {
        for (i = prevIndex; i <= text_idx; i++) {
            if (text_buffer[i] == '\n') {
                newLines++;
                lineIdx = 0;
                int j;
              
                //post to AWS
                aws_post_message((const char *)text_buffer, lRetVal);

                fillRect(10, lineHeight, 6*text_idx, 8, BLACK);
                text_idx = 0;
                text_buffer[0] = '\0';

                DecoderVal.sameButtonCount = 0;
                DecoderVal.logButtonCount = 0;

                DecoderVal.letter = '?';
                DecoderVal.previousButton = 0;

                DecoderVal.timerStarter = 0;


            } else {
                int cursor_x = 10 + lineIdx*6;
                int cursor_y = lineHeight + newLines * 12;
                unsigned char character = text_buffer[i];
                drawChar(cursor_x, cursor_y, character, TEXT_COLOR_PALET[DecoderVal.colorPalet], BLACK, 1);
                lineIdx++;

            }
        }

    } else if (prevIndex > text_idx) {
        IntMasterDisable();
        for (i = prevIndex; i > text_idx; i--) {
            fillRect(10 + lineIdx*6, lineHeight + newLines*12, 10, 10, BLACK);
            lineIdx--;
        }
        IntMasterEnable();

    } else if (prevIndex == text_idx) {
        if (inPlaceTextCount == 8) {
        } else if (inPlaceTextCount == 9) {
            int cursor_x = 10 + lineIdx*6;
            int cursor_y = lineHeight + newLines * 12;
            //IntMasterDisable();
            if (text_buffer[i] != '\n') {
                IntMasterDisable();
                fillRect(cursor_x, cursor_y, 6, 8, BLACK);
                drawChar(cursor_x, cursor_y, text_buffer[i], TEXT_COLOR_PALET[DecoderVal.colorPalet], BLACK, 1);
                IntMasterEnable();
            }
            //IntMasterEnable();
            inPlaceTextCount = 0;
        }

        inPlaceTextCount++;
    }


    prevIndex = i;
}

void DisplayRecieverText() {
    static int prevIndex = 0;
    if (prevIndex == recv_idx) {
        return;
    }

    IntMasterDisable();

    unsigned char recv_text[64];
    int i;

    for (i = UART_START_CMD_SIZE; i < recv_idx; i++) {
        recv_text[i - UART_START_CMD_SIZE] = recv_buffer[i];
    }
    recv_text[i - 1] = '\0';
    //printf("Printing: %s", recv_text);

    if (recv_buffer_reset == 1) {
        fillRect(10, 10, prevIndex*6, 10, BLACK);
        int j;
        int cursor_x = 10;
        int cursor_y = 10;
        for (j = 0; j < i; j++) {
            drawChar(cursor_x, cursor_y, recv_text[j], TEXT_COLOR_PALET[DecoderVal.colorPalet], BLACK, 1);
            cursor_x += 6;
        }
        recv_buffer_reset = 0;
    }

    prevIndex = recv_idx;

    IntMasterEnable();
}

//*****************************************************************************
// AWS IoT / Networking LAB4 with extended time
//*****************************************************************************

// We update this to actual date/time every run
#define DATE    25
#define MONTH   2
#define YEAR    2025
#define HOUR    1
#define MINUTE  33
#define SECOND  0

#define APPLICATION_NAME      "SSL"
#define APPLICATION_VERSION   "SQ24"
#define SERVER_NAME           "a25abq9uai3xbf-ats.iot.us-east-1.amazonaws.com"
#define GOOGLE_DST_PORT       8443

#define POSTHEADER "POST /things/Ayub_CC3200_Board/shadow HTTP/1.1\r\n"
#define HOSTHEADER "Host: a25abq9uai3xbf-ats.iot.us-east-1.amazonaws.com\r\n"
#define CHEADER    "Connection: Keep-Alive\r\n"
#define CTHEADER   "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1  "Content-Length: "
#define CLHEADER2  "\r\n\r\n"

#define DATA1  "{" \
               "\"state\": {\r\n"                                              \
                  "\"desired\" : {\r\n"                                       \
                      "\"var\" :\""                                           \
                      "Hello phone, message from CC3200 via AWS IoT!"         \
                      "\"\r\n"                                                \
                  "}"                                                         \
               "}"                                                             \
             "}\r\n\r\n"


#if defined(ccs) || defined(gcc)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

// local prototypes
static int set_time();
static void BoardInit(void);
static int http_post(int iTLSSockID);

/******************************************************************************
 * BoardInit
 ******************************************************************************/
static void BoardInit(void) {
#ifndef USE_TIRTOS
  #if defined(ccs)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
  #endif
  #if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
  #endif
#endif
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);
    PRCMCC3200MCUInit();
}

/******************************************************************************
 * http_post (unused in your final code, but left as is)
 ******************************************************************************/
static int http_post(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int dataLength = strlen(DATA1);

    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);
    strcpy(pcBufHeaders, CLHEADER1);

    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);

    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);

    strcpy(pcBufHeaders, DATA1);
    pcBufHeaders += strlen(DATA1);

    UART_PRINT(acSendBuff);

    // Send the packet to the server
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("POST failed. Error Number: %i\n\r",lRetVal);
        sl_Close(iTLSSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    } else {
        acRecvbuff[lRetVal+1] = '\0';
        UART_PRINT(acRecvbuff);
        UART_PRINT("\n\r\n\r");
    }
    return 0;
}

/******************************************************************************
 * set_time
 ******************************************************************************/
static int set_time() {
    long retVal;
    g_time.tm_day  = DATE;
    g_time.tm_mon  = MONTH;
    g_time.tm_year = YEAR;
    g_time.tm_sec  = HOUR;
    g_time.tm_hour = MINUTE;
    g_time.tm_min  = SECOND;

    retVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION,
                       SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                       sizeof(SlDateTime),(unsigned char *)(&g_time));

    ASSERT_ON_ERROR(retVal);
    return SUCCESS;
}

/******************************************************************************
 * aws_post_message
 * Helper to build a JSON payload from 'msg' and do an HTTP POST to AWS IoT
 ******************************************************************************/
static int aws_post_message(const char *msg, int sockID)
{
    int lRetVal;
    char acSendBuff[512];
    char acRecvBuff[1460];
    char cCLLength[50];
    char jsonPayload[256];
    char *pcBufHeaders;

    printf("inside aws\n");

    if (sockID < 0) {
        UART_PRINT("TLS connect failed in aws_post_message\n\r");
        return sockID;
    }

    // 1) Copy 'msg' into a local buffer so we can strip trailing '\n' or '\r'
    char localMsg[64];
    strncpy(localMsg, msg, sizeof(localMsg)-1);
    localMsg[sizeof(localMsg)-1] = '\0';

    // then remove trailing newline
    int length = strlen(localMsg);
    while (length > 0 && (localMsg[length-1]=='\n' || localMsg[length-1]=='\r')) {
        localMsg[length-1] = '\0';
        length--;
    }

    // 2) making sure we build JSON payload --WITHOUT-- extra newlines
    // example: {"state":{"desired":{"var":"HELLO"}}}
    snprintf(jsonPayload, sizeof(jsonPayload),
             "{\"state\":{\"desired\":{\"var\":\"%s\"}}}", localMsg);

    // 3) we build HTTP POST
    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, "POST /things/Ayub_CC3200_Board/shadow HTTP/1.1\r\n");
    pcBufHeaders += strlen(pcBufHeaders);
    strcpy(pcBufHeaders, "Host: a25abq9uai3xbf-ats.iot.us-east-1.amazonaws.com\r\n");
    pcBufHeaders += strlen(pcBufHeaders);
    strcpy(pcBufHeaders, "Connection: Keep-Alive\r\n");
    pcBufHeaders += strlen(pcBufHeaders);
    strcpy(pcBufHeaders, "Content-Type: application/json; charset=utf-8\r\n");
    pcBufHeaders += strlen(pcBufHeaders);

    // 4) find the Content-Length
    sprintf(cCLLength, "Content-Length: %d\r\n\r\n", (int)strlen(jsonPayload));
    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);

    // 5) Append JSON
    strcpy(pcBufHeaders, jsonPayload);

    UART_PRINT("Sending to AWS:\n\r%s\n\r", acSendBuff);

    // 6) we then send the POST
    lRetVal = sl_Send(sockID, acSendBuff, strlen(acSendBuff), 0);
    if (lRetVal < 0) {
        UART_PRINT("AWS POST send failed: %d\n\r", lRetVal);
        sl_Close(sockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }

    printf("inside aws before response\n");

    // 7) We receive the response
    lRetVal = sl_Recv(sockID, acRecvBuff, sizeof(acRecvBuff), 0);
    if (lRetVal < 0) {
        printf("inside fail response\n");
        UART_PRINT("AWS POST recv failed: %d\n\r", lRetVal);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    printf("after response\n");
    acRecvBuff[lRetVal] = '\0';
    UART_PRINT("AWS POST Response:\n\r%s\n\r", acRecvBuff);
    printf("before return\n");
    return 0;
}

static int aws_get_message(int sockID)
{
    int lRetVal;
    char acSendBuff[512];
    char acRecvBuff[1460];
    char *pcBufHeaders;

    printf("inside aws_get_message\n");

    if (sockID < 0) {
        UART_PRINT("TLS connect failed in aws_get_message\n\r");
        return sockID;
    }

    // 1) Build HTTP GET Request using the demo and then need to change only somethings
    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, "GET /things/Ayub_CC3200_Board/shadow HTTP/1.1\r\n");
    pcBufHeaders += strlen(pcBufHeaders);
    strcpy(pcBufHeaders, "Host: a25abq9uai3xbf-ats.iot.us-east-1.amazonaws.com\r\n");
    pcBufHeaders += strlen(pcBufHeaders);
    strcpy(pcBufHeaders, "Connection: Keep-Alive\r\n\r\n");

    UART_PRINT("Sending GET request to AWS:\n\r%s\n\r", acSendBuff);

    // 2) we then send the GET request
    lRetVal = sl_Send(sockID, acSendBuff, strlen(acSendBuff), 0);
    if (lRetVal < 0) {
        UART_PRINT("AWS GET send failed: %d\n\r", lRetVal);
        sl_Close(sockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }

    printf("inside aws_get_message before response\n");

    // 3) We receive the response here
    lRetVal = sl_Recv(sockID, acRecvBuff, sizeof(acRecvBuff), 0);
    if (lRetVal < 0) {
        printf("inside fail response\n");
        UART_PRINT("AWS GET recv failed: %d\n\r", lRetVal);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    printf("after response\n");
    acRecvBuff[lRetVal] = '\0';
    UART_PRINT("AWS GET Response:\n\r%s\n\r", acRecvBuff);
    printf("before return\n");
    return 0;
}


//*****************************************************************************
// Initialize hardware modules
//*****************************************************************************

static void SPIInit(void) {
    MAP_PRCMPeripheralClkEnable(PRCM_GSPI, PRCM_RUN_MODE_CLK);
    MAP_PRCMPeripheralReset(PRCM_GSPI);
    MAP_SPIReset(GSPI_BASE);

    MAP_SPIFIFOEnable(GSPI_BASE, SPI_TX_FIFO || SPI_RX_FIFO);

    MAP_SPIConfigSetExpClk(GSPI_BASE,
                           MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                           SPI_IF_BIT_RATE,
                           SPI_MODE_MASTER,
                           SPI_SUB_MODE_0,
                           (SPI_SW_CTRL_CS |
                            SPI_4PIN_MODE |
                            SPI_TURBO_ON |
                            SPI_CS_ACTIVEHIGH |
                            SPI_WL_8));
    MAP_SPIEnable(GSPI_BASE);
}

static void IRRecieverInit(void) {
    MAP_GPIOIntRegister(IR_GPIO_PORT, GPIOA3IntHandler);
    MAP_GPIOIntTypeSet(IR_GPIO_PORT, IR_GPIO_PIN, GPIO_BOTH_EDGES);
    uint64_t ulStatus = MAP_GPIOIntStatus(IR_GPIO_PORT, false);
    MAP_GPIOIntClear(IR_GPIO_PORT, IR_GPIO_PIN);
    MAP_GPIOIntEnable(IR_GPIO_PORT, IR_GPIO_PIN);
}

static void UARTInit(void) {
    PRCMPeripheralReset(PRCM_UARTA1);
    UARTConfigSetExpClk(UARTA1_BASE,
                        PRCMPeripheralClockGet(PRCM_UARTA1),
                        UART_BAUD_RATE,
                        (UART_CONFIG_WLEN_8 | UART_CONFIG_STOP_ONE | UART_CONFIG_PAR_NONE));

    UARTIntRegister(UARTA1_BASE, UARTIntHandler);
    UARTIntEnable(UARTA1_BASE, UART_INT_RX);
    UARTFIFOLevelSet(UARTA1_BASE, UART_FIFO_TX1_8, UART_FIFO_RX1_8);
    UARTEnable(UARTA1_BASE);
}

static void SysTickInit(void) {
    MAP_SysTickPeriodSet(SYSTICK_RELOAD_VAL * 4);
    MAP_SysTickIntRegister(SysTickHandler);
    MAP_SysTickIntEnable();
    // We do NOT enable SysTick immediately; we only start it in the IR handler.
}

static void SysTimerInit(void) {
    g_ulBase = TIMERA0_BASE;
    Timer_IF_Init(PRCM_TIMERA0, g_ulBase, TIMER_CFG_PERIODIC, TIMER_A, 0);
    Timer_IF_IntSetup(g_ulBase, TIMER_A, SysTimerHandler);
}

//*****************************************************************************
// Main
//*****************************************************************************
void main() {
    long lRetVal = -1;

    // Initialize board config
    BoardInit();

    // Muxing UART and SPI lines
    PinMuxConfig();

    // Initialize the Terminal
    InitTerm();
    ClearTerm();
    UART_PRINT("My terminal works!\n\r");

    // Initialize other modules
    UARTInit();
    SPIInit();
    IRRecieverInit();
    SysTickInit();
    SysTimerInit();

    // CC3200 to Wi-Fi, TLS to AWS
    g_app_config.host = SERVER_NAME;
    g_app_config.port = GOOGLE_DST_PORT;

    lRetVal = connectToAccessPoint(); 
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device\n\r");
        LOOP_FOREVER();
    }
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }

    //http_post(lRetVal);
    Adafruit_Init();
    fillScreen(BLACK);
    drawLine(0, 64, 128, 64, WHITE);
    while (1) {
        UtilsDelay(1000000);
        DisplaySenderText(lRetVal);
        //DisplayRecieverText();
    }

    printf("here before stop \n");
    //sl_Stop(SL_STOP_TIMEOUT);
    //LOOP_FOREVER();
    printf("After it loop \n");
}
