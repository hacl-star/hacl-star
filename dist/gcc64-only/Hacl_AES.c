/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_AES.h"

static uint8_t multiply(uint8_t a, uint8_t b)
{
  return
    a
    * (b & (uint8_t)1U)
    ^
      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
      * (b >> (uint32_t)1U & (uint8_t)1U)
      ^
        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
        << (uint32_t)1U
        ^
          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
          >> (uint32_t)7U
          & (uint8_t)1U)
          * (uint8_t)0x1bU)
        * (b >> (uint32_t)2U & (uint8_t)1U)
        ^
          ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
          << (uint32_t)1U
          ^
            ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            >> (uint32_t)7U
            & (uint8_t)1U)
            * (uint8_t)0x1bU)
          << (uint32_t)1U
          ^
            (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            >> (uint32_t)7U
            & (uint8_t)1U)
            * (uint8_t)0x1bU)
          * (b >> (uint32_t)3U & (uint8_t)1U)
          ^
            (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            * (b >> (uint32_t)4U & (uint8_t)1U)
            ^
              ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              * (b >> (uint32_t)5U & (uint8_t)1U)
              ^
                (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                * (b >> (uint32_t)6U & (uint8_t)1U)
                ^
                  (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((((a
                          << (uint32_t)1U
                          ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            (((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            << (uint32_t)1U
                            ^
                              ((a
                              << (uint32_t)1U
                              ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                              >> (uint32_t)7U
                              & (uint8_t)1U)
                              * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  * (b >> (uint32_t)7U & (uint8_t)1U)))))));
}

void Crypto_Symmetric_AES_mk_sbox(uint8_t *sbox)
{
  sbox[0U] = (uint8_t)0x63U;
  sbox[1U] = (uint8_t)0x7cU;
  sbox[2U] = (uint8_t)0x77U;
  sbox[3U] = (uint8_t)0x7bU;
  sbox[4U] = (uint8_t)0xf2U;
  sbox[5U] = (uint8_t)0x6bU;
  sbox[6U] = (uint8_t)0x6fU;
  sbox[7U] = (uint8_t)0xc5U;
  sbox[8U] = (uint8_t)0x30U;
  sbox[9U] = (uint8_t)0x01U;
  sbox[10U] = (uint8_t)0x67U;
  sbox[11U] = (uint8_t)0x2bU;
  sbox[12U] = (uint8_t)0xfeU;
  sbox[13U] = (uint8_t)0xd7U;
  sbox[14U] = (uint8_t)0xabU;
  sbox[15U] = (uint8_t)0x76U;
  sbox[16U] = (uint8_t)0xcaU;
  sbox[17U] = (uint8_t)0x82U;
  sbox[18U] = (uint8_t)0xc9U;
  sbox[19U] = (uint8_t)0x7dU;
  sbox[20U] = (uint8_t)0xfaU;
  sbox[21U] = (uint8_t)0x59U;
  sbox[22U] = (uint8_t)0x47U;
  sbox[23U] = (uint8_t)0xf0U;
  sbox[24U] = (uint8_t)0xadU;
  sbox[25U] = (uint8_t)0xd4U;
  sbox[26U] = (uint8_t)0xa2U;
  sbox[27U] = (uint8_t)0xafU;
  sbox[28U] = (uint8_t)0x9cU;
  sbox[29U] = (uint8_t)0xa4U;
  sbox[30U] = (uint8_t)0x72U;
  sbox[31U] = (uint8_t)0xc0U;
  sbox[32U] = (uint8_t)0xb7U;
  sbox[33U] = (uint8_t)0xfdU;
  sbox[34U] = (uint8_t)0x93U;
  sbox[35U] = (uint8_t)0x26U;
  sbox[36U] = (uint8_t)0x36U;
  sbox[37U] = (uint8_t)0x3fU;
  sbox[38U] = (uint8_t)0xf7U;
  sbox[39U] = (uint8_t)0xccU;
  sbox[40U] = (uint8_t)0x34U;
  sbox[41U] = (uint8_t)0xa5U;
  sbox[42U] = (uint8_t)0xe5U;
  sbox[43U] = (uint8_t)0xf1U;
  sbox[44U] = (uint8_t)0x71U;
  sbox[45U] = (uint8_t)0xd8U;
  sbox[46U] = (uint8_t)0x31U;
  sbox[47U] = (uint8_t)0x15U;
  sbox[48U] = (uint8_t)0x04U;
  sbox[49U] = (uint8_t)0xc7U;
  sbox[50U] = (uint8_t)0x23U;
  sbox[51U] = (uint8_t)0xc3U;
  sbox[52U] = (uint8_t)0x18U;
  sbox[53U] = (uint8_t)0x96U;
  sbox[54U] = (uint8_t)0x05U;
  sbox[55U] = (uint8_t)0x9aU;
  sbox[56U] = (uint8_t)0x07U;
  sbox[57U] = (uint8_t)0x12U;
  sbox[58U] = (uint8_t)0x80U;
  sbox[59U] = (uint8_t)0xe2U;
  sbox[60U] = (uint8_t)0xebU;
  sbox[61U] = (uint8_t)0x27U;
  sbox[62U] = (uint8_t)0xb2U;
  sbox[63U] = (uint8_t)0x75U;
  sbox[64U] = (uint8_t)0x09U;
  sbox[65U] = (uint8_t)0x83U;
  sbox[66U] = (uint8_t)0x2cU;
  sbox[67U] = (uint8_t)0x1aU;
  sbox[68U] = (uint8_t)0x1bU;
  sbox[69U] = (uint8_t)0x6eU;
  sbox[70U] = (uint8_t)0x5aU;
  sbox[71U] = (uint8_t)0xa0U;
  sbox[72U] = (uint8_t)0x52U;
  sbox[73U] = (uint8_t)0x3bU;
  sbox[74U] = (uint8_t)0xd6U;
  sbox[75U] = (uint8_t)0xb3U;
  sbox[76U] = (uint8_t)0x29U;
  sbox[77U] = (uint8_t)0xe3U;
  sbox[78U] = (uint8_t)0x2fU;
  sbox[79U] = (uint8_t)0x84U;
  sbox[80U] = (uint8_t)0x53U;
  sbox[81U] = (uint8_t)0xd1U;
  sbox[82U] = (uint8_t)0x00U;
  sbox[83U] = (uint8_t)0xedU;
  sbox[84U] = (uint8_t)0x20U;
  sbox[85U] = (uint8_t)0xfcU;
  sbox[86U] = (uint8_t)0xb1U;
  sbox[87U] = (uint8_t)0x5bU;
  sbox[88U] = (uint8_t)0x6aU;
  sbox[89U] = (uint8_t)0xcbU;
  sbox[90U] = (uint8_t)0xbeU;
  sbox[91U] = (uint8_t)0x39U;
  sbox[92U] = (uint8_t)0x4aU;
  sbox[93U] = (uint8_t)0x4cU;
  sbox[94U] = (uint8_t)0x58U;
  sbox[95U] = (uint8_t)0xcfU;
  sbox[96U] = (uint8_t)0xd0U;
  sbox[97U] = (uint8_t)0xefU;
  sbox[98U] = (uint8_t)0xaaU;
  sbox[99U] = (uint8_t)0xfbU;
  sbox[100U] = (uint8_t)0x43U;
  sbox[101U] = (uint8_t)0x4dU;
  sbox[102U] = (uint8_t)0x33U;
  sbox[103U] = (uint8_t)0x85U;
  sbox[104U] = (uint8_t)0x45U;
  sbox[105U] = (uint8_t)0xf9U;
  sbox[106U] = (uint8_t)0x02U;
  sbox[107U] = (uint8_t)0x7fU;
  sbox[108U] = (uint8_t)0x50U;
  sbox[109U] = (uint8_t)0x3cU;
  sbox[110U] = (uint8_t)0x9fU;
  sbox[111U] = (uint8_t)0xa8U;
  sbox[112U] = (uint8_t)0x51U;
  sbox[113U] = (uint8_t)0xa3U;
  sbox[114U] = (uint8_t)0x40U;
  sbox[115U] = (uint8_t)0x8fU;
  sbox[116U] = (uint8_t)0x92U;
  sbox[117U] = (uint8_t)0x9dU;
  sbox[118U] = (uint8_t)0x38U;
  sbox[119U] = (uint8_t)0xf5U;
  sbox[120U] = (uint8_t)0xbcU;
  sbox[121U] = (uint8_t)0xb6U;
  sbox[122U] = (uint8_t)0xdaU;
  sbox[123U] = (uint8_t)0x21U;
  sbox[124U] = (uint8_t)0x10U;
  sbox[125U] = (uint8_t)0xffU;
  sbox[126U] = (uint8_t)0xf3U;
  sbox[127U] = (uint8_t)0xd2U;
  sbox[128U] = (uint8_t)0xcdU;
  sbox[129U] = (uint8_t)0x0cU;
  sbox[130U] = (uint8_t)0x13U;
  sbox[131U] = (uint8_t)0xecU;
  sbox[132U] = (uint8_t)0x5fU;
  sbox[133U] = (uint8_t)0x97U;
  sbox[134U] = (uint8_t)0x44U;
  sbox[135U] = (uint8_t)0x17U;
  sbox[136U] = (uint8_t)0xc4U;
  sbox[137U] = (uint8_t)0xa7U;
  sbox[138U] = (uint8_t)0x7eU;
  sbox[139U] = (uint8_t)0x3dU;
  sbox[140U] = (uint8_t)0x64U;
  sbox[141U] = (uint8_t)0x5dU;
  sbox[142U] = (uint8_t)0x19U;
  sbox[143U] = (uint8_t)0x73U;
  sbox[144U] = (uint8_t)0x60U;
  sbox[145U] = (uint8_t)0x81U;
  sbox[146U] = (uint8_t)0x4fU;
  sbox[147U] = (uint8_t)0xdcU;
  sbox[148U] = (uint8_t)0x22U;
  sbox[149U] = (uint8_t)0x2aU;
  sbox[150U] = (uint8_t)0x90U;
  sbox[151U] = (uint8_t)0x88U;
  sbox[152U] = (uint8_t)0x46U;
  sbox[153U] = (uint8_t)0xeeU;
  sbox[154U] = (uint8_t)0xb8U;
  sbox[155U] = (uint8_t)0x14U;
  sbox[156U] = (uint8_t)0xdeU;
  sbox[157U] = (uint8_t)0x5eU;
  sbox[158U] = (uint8_t)0x0bU;
  sbox[159U] = (uint8_t)0xdbU;
  sbox[160U] = (uint8_t)0xe0U;
  sbox[161U] = (uint8_t)0x32U;
  sbox[162U] = (uint8_t)0x3aU;
  sbox[163U] = (uint8_t)0x0aU;
  sbox[164U] = (uint8_t)0x49U;
  sbox[165U] = (uint8_t)0x06U;
  sbox[166U] = (uint8_t)0x24U;
  sbox[167U] = (uint8_t)0x5cU;
  sbox[168U] = (uint8_t)0xc2U;
  sbox[169U] = (uint8_t)0xd3U;
  sbox[170U] = (uint8_t)0xacU;
  sbox[171U] = (uint8_t)0x62U;
  sbox[172U] = (uint8_t)0x91U;
  sbox[173U] = (uint8_t)0x95U;
  sbox[174U] = (uint8_t)0xe4U;
  sbox[175U] = (uint8_t)0x79U;
  sbox[176U] = (uint8_t)0xe7U;
  sbox[177U] = (uint8_t)0xc8U;
  sbox[178U] = (uint8_t)0x37U;
  sbox[179U] = (uint8_t)0x6dU;
  sbox[180U] = (uint8_t)0x8dU;
  sbox[181U] = (uint8_t)0xd5U;
  sbox[182U] = (uint8_t)0x4eU;
  sbox[183U] = (uint8_t)0xa9U;
  sbox[184U] = (uint8_t)0x6cU;
  sbox[185U] = (uint8_t)0x56U;
  sbox[186U] = (uint8_t)0xf4U;
  sbox[187U] = (uint8_t)0xeaU;
  sbox[188U] = (uint8_t)0x65U;
  sbox[189U] = (uint8_t)0x7aU;
  sbox[190U] = (uint8_t)0xaeU;
  sbox[191U] = (uint8_t)0x08U;
  sbox[192U] = (uint8_t)0xbaU;
  sbox[193U] = (uint8_t)0x78U;
  sbox[194U] = (uint8_t)0x25U;
  sbox[195U] = (uint8_t)0x2eU;
  sbox[196U] = (uint8_t)0x1cU;
  sbox[197U] = (uint8_t)0xa6U;
  sbox[198U] = (uint8_t)0xb4U;
  sbox[199U] = (uint8_t)0xc6U;
  sbox[200U] = (uint8_t)0xe8U;
  sbox[201U] = (uint8_t)0xddU;
  sbox[202U] = (uint8_t)0x74U;
  sbox[203U] = (uint8_t)0x1fU;
  sbox[204U] = (uint8_t)0x4bU;
  sbox[205U] = (uint8_t)0xbdU;
  sbox[206U] = (uint8_t)0x8bU;
  sbox[207U] = (uint8_t)0x8aU;
  sbox[208U] = (uint8_t)0x70U;
  sbox[209U] = (uint8_t)0x3eU;
  sbox[210U] = (uint8_t)0xb5U;
  sbox[211U] = (uint8_t)0x66U;
  sbox[212U] = (uint8_t)0x48U;
  sbox[213U] = (uint8_t)0x03U;
  sbox[214U] = (uint8_t)0xf6U;
  sbox[215U] = (uint8_t)0x0eU;
  sbox[216U] = (uint8_t)0x61U;
  sbox[217U] = (uint8_t)0x35U;
  sbox[218U] = (uint8_t)0x57U;
  sbox[219U] = (uint8_t)0xb9U;
  sbox[220U] = (uint8_t)0x86U;
  sbox[221U] = (uint8_t)0xc1U;
  sbox[222U] = (uint8_t)0x1dU;
  sbox[223U] = (uint8_t)0x9eU;
  sbox[224U] = (uint8_t)0xe1U;
  sbox[225U] = (uint8_t)0xf8U;
  sbox[226U] = (uint8_t)0x98U;
  sbox[227U] = (uint8_t)0x11U;
  sbox[228U] = (uint8_t)0x69U;
  sbox[229U] = (uint8_t)0xd9U;
  sbox[230U] = (uint8_t)0x8eU;
  sbox[231U] = (uint8_t)0x94U;
  sbox[232U] = (uint8_t)0x9bU;
  sbox[233U] = (uint8_t)0x1eU;
  sbox[234U] = (uint8_t)0x87U;
  sbox[235U] = (uint8_t)0xe9U;
  sbox[236U] = (uint8_t)0xceU;
  sbox[237U] = (uint8_t)0x55U;
  sbox[238U] = (uint8_t)0x28U;
  sbox[239U] = (uint8_t)0xdfU;
  sbox[240U] = (uint8_t)0x8cU;
  sbox[241U] = (uint8_t)0xa1U;
  sbox[242U] = (uint8_t)0x89U;
  sbox[243U] = (uint8_t)0x0dU;
  sbox[244U] = (uint8_t)0xbfU;
  sbox[245U] = (uint8_t)0xe6U;
  sbox[246U] = (uint8_t)0x42U;
  sbox[247U] = (uint8_t)0x68U;
  sbox[248U] = (uint8_t)0x41U;
  sbox[249U] = (uint8_t)0x99U;
  sbox[250U] = (uint8_t)0x2dU;
  sbox[251U] = (uint8_t)0x0fU;
  sbox[252U] = (uint8_t)0xb0U;
  sbox[253U] = (uint8_t)0x54U;
  sbox[254U] = (uint8_t)0xbbU;
  sbox[255U] = (uint8_t)0x16U;
}

void Crypto_Symmetric_AES_mk_inv_sbox(uint8_t *sbox)
{
  sbox[0U] = (uint8_t)0x52U;
  sbox[1U] = (uint8_t)0x09U;
  sbox[2U] = (uint8_t)0x6aU;
  sbox[3U] = (uint8_t)0xd5U;
  sbox[4U] = (uint8_t)0x30U;
  sbox[5U] = (uint8_t)0x36U;
  sbox[6U] = (uint8_t)0xa5U;
  sbox[7U] = (uint8_t)0x38U;
  sbox[8U] = (uint8_t)0xbfU;
  sbox[9U] = (uint8_t)0x40U;
  sbox[10U] = (uint8_t)0xa3U;
  sbox[11U] = (uint8_t)0x9eU;
  sbox[12U] = (uint8_t)0x81U;
  sbox[13U] = (uint8_t)0xf3U;
  sbox[14U] = (uint8_t)0xd7U;
  sbox[15U] = (uint8_t)0xfbU;
  sbox[16U] = (uint8_t)0x7cU;
  sbox[17U] = (uint8_t)0xe3U;
  sbox[18U] = (uint8_t)0x39U;
  sbox[19U] = (uint8_t)0x82U;
  sbox[20U] = (uint8_t)0x9bU;
  sbox[21U] = (uint8_t)0x2fU;
  sbox[22U] = (uint8_t)0xffU;
  sbox[23U] = (uint8_t)0x87U;
  sbox[24U] = (uint8_t)0x34U;
  sbox[25U] = (uint8_t)0x8eU;
  sbox[26U] = (uint8_t)0x43U;
  sbox[27U] = (uint8_t)0x44U;
  sbox[28U] = (uint8_t)0xc4U;
  sbox[29U] = (uint8_t)0xdeU;
  sbox[30U] = (uint8_t)0xe9U;
  sbox[31U] = (uint8_t)0xcbU;
  sbox[32U] = (uint8_t)0x54U;
  sbox[33U] = (uint8_t)0x7bU;
  sbox[34U] = (uint8_t)0x94U;
  sbox[35U] = (uint8_t)0x32U;
  sbox[36U] = (uint8_t)0xa6U;
  sbox[37U] = (uint8_t)0xc2U;
  sbox[38U] = (uint8_t)0x23U;
  sbox[39U] = (uint8_t)0x3dU;
  sbox[40U] = (uint8_t)0xeeU;
  sbox[41U] = (uint8_t)0x4cU;
  sbox[42U] = (uint8_t)0x95U;
  sbox[43U] = (uint8_t)0x0bU;
  sbox[44U] = (uint8_t)0x42U;
  sbox[45U] = (uint8_t)0xfaU;
  sbox[46U] = (uint8_t)0xc3U;
  sbox[47U] = (uint8_t)0x4eU;
  sbox[48U] = (uint8_t)0x08U;
  sbox[49U] = (uint8_t)0x2eU;
  sbox[50U] = (uint8_t)0xa1U;
  sbox[51U] = (uint8_t)0x66U;
  sbox[52U] = (uint8_t)0x28U;
  sbox[53U] = (uint8_t)0xd9U;
  sbox[54U] = (uint8_t)0x24U;
  sbox[55U] = (uint8_t)0xb2U;
  sbox[56U] = (uint8_t)0x76U;
  sbox[57U] = (uint8_t)0x5bU;
  sbox[58U] = (uint8_t)0xa2U;
  sbox[59U] = (uint8_t)0x49U;
  sbox[60U] = (uint8_t)0x6dU;
  sbox[61U] = (uint8_t)0x8bU;
  sbox[62U] = (uint8_t)0xd1U;
  sbox[63U] = (uint8_t)0x25U;
  sbox[64U] = (uint8_t)0x72U;
  sbox[65U] = (uint8_t)0xf8U;
  sbox[66U] = (uint8_t)0xf6U;
  sbox[67U] = (uint8_t)0x64U;
  sbox[68U] = (uint8_t)0x86U;
  sbox[69U] = (uint8_t)0x68U;
  sbox[70U] = (uint8_t)0x98U;
  sbox[71U] = (uint8_t)0x16U;
  sbox[72U] = (uint8_t)0xd4U;
  sbox[73U] = (uint8_t)0xa4U;
  sbox[74U] = (uint8_t)0x5cU;
  sbox[75U] = (uint8_t)0xccU;
  sbox[76U] = (uint8_t)0x5dU;
  sbox[77U] = (uint8_t)0x65U;
  sbox[78U] = (uint8_t)0xb6U;
  sbox[79U] = (uint8_t)0x92U;
  sbox[80U] = (uint8_t)0x6cU;
  sbox[81U] = (uint8_t)0x70U;
  sbox[82U] = (uint8_t)0x48U;
  sbox[83U] = (uint8_t)0x50U;
  sbox[84U] = (uint8_t)0xfdU;
  sbox[85U] = (uint8_t)0xedU;
  sbox[86U] = (uint8_t)0xb9U;
  sbox[87U] = (uint8_t)0xdaU;
  sbox[88U] = (uint8_t)0x5eU;
  sbox[89U] = (uint8_t)0x15U;
  sbox[90U] = (uint8_t)0x46U;
  sbox[91U] = (uint8_t)0x57U;
  sbox[92U] = (uint8_t)0xa7U;
  sbox[93U] = (uint8_t)0x8dU;
  sbox[94U] = (uint8_t)0x9dU;
  sbox[95U] = (uint8_t)0x84U;
  sbox[96U] = (uint8_t)0x90U;
  sbox[97U] = (uint8_t)0xd8U;
  sbox[98U] = (uint8_t)0xabU;
  sbox[99U] = (uint8_t)0x00U;
  sbox[100U] = (uint8_t)0x8cU;
  sbox[101U] = (uint8_t)0xbcU;
  sbox[102U] = (uint8_t)0xd3U;
  sbox[103U] = (uint8_t)0x0aU;
  sbox[104U] = (uint8_t)0xf7U;
  sbox[105U] = (uint8_t)0xe4U;
  sbox[106U] = (uint8_t)0x58U;
  sbox[107U] = (uint8_t)0x05U;
  sbox[108U] = (uint8_t)0xb8U;
  sbox[109U] = (uint8_t)0xb3U;
  sbox[110U] = (uint8_t)0x45U;
  sbox[111U] = (uint8_t)0x06U;
  sbox[112U] = (uint8_t)0xd0U;
  sbox[113U] = (uint8_t)0x2cU;
  sbox[114U] = (uint8_t)0x1eU;
  sbox[115U] = (uint8_t)0x8fU;
  sbox[116U] = (uint8_t)0xcaU;
  sbox[117U] = (uint8_t)0x3fU;
  sbox[118U] = (uint8_t)0x0fU;
  sbox[119U] = (uint8_t)0x02U;
  sbox[120U] = (uint8_t)0xc1U;
  sbox[121U] = (uint8_t)0xafU;
  sbox[122U] = (uint8_t)0xbdU;
  sbox[123U] = (uint8_t)0x03U;
  sbox[124U] = (uint8_t)0x01U;
  sbox[125U] = (uint8_t)0x13U;
  sbox[126U] = (uint8_t)0x8aU;
  sbox[127U] = (uint8_t)0x6bU;
  sbox[128U] = (uint8_t)0x3aU;
  sbox[129U] = (uint8_t)0x91U;
  sbox[130U] = (uint8_t)0x11U;
  sbox[131U] = (uint8_t)0x41U;
  sbox[132U] = (uint8_t)0x4fU;
  sbox[133U] = (uint8_t)0x67U;
  sbox[134U] = (uint8_t)0xdcU;
  sbox[135U] = (uint8_t)0xeaU;
  sbox[136U] = (uint8_t)0x97U;
  sbox[137U] = (uint8_t)0xf2U;
  sbox[138U] = (uint8_t)0xcfU;
  sbox[139U] = (uint8_t)0xceU;
  sbox[140U] = (uint8_t)0xf0U;
  sbox[141U] = (uint8_t)0xb4U;
  sbox[142U] = (uint8_t)0xe6U;
  sbox[143U] = (uint8_t)0x73U;
  sbox[144U] = (uint8_t)0x96U;
  sbox[145U] = (uint8_t)0xacU;
  sbox[146U] = (uint8_t)0x74U;
  sbox[147U] = (uint8_t)0x22U;
  sbox[148U] = (uint8_t)0xe7U;
  sbox[149U] = (uint8_t)0xadU;
  sbox[150U] = (uint8_t)0x35U;
  sbox[151U] = (uint8_t)0x85U;
  sbox[152U] = (uint8_t)0xe2U;
  sbox[153U] = (uint8_t)0xf9U;
  sbox[154U] = (uint8_t)0x37U;
  sbox[155U] = (uint8_t)0xe8U;
  sbox[156U] = (uint8_t)0x1cU;
  sbox[157U] = (uint8_t)0x75U;
  sbox[158U] = (uint8_t)0xdfU;
  sbox[159U] = (uint8_t)0x6eU;
  sbox[160U] = (uint8_t)0x47U;
  sbox[161U] = (uint8_t)0xf1U;
  sbox[162U] = (uint8_t)0x1aU;
  sbox[163U] = (uint8_t)0x71U;
  sbox[164U] = (uint8_t)0x1dU;
  sbox[165U] = (uint8_t)0x29U;
  sbox[166U] = (uint8_t)0xc5U;
  sbox[167U] = (uint8_t)0x89U;
  sbox[168U] = (uint8_t)0x6fU;
  sbox[169U] = (uint8_t)0xb7U;
  sbox[170U] = (uint8_t)0x62U;
  sbox[171U] = (uint8_t)0x0eU;
  sbox[172U] = (uint8_t)0xaaU;
  sbox[173U] = (uint8_t)0x18U;
  sbox[174U] = (uint8_t)0xbeU;
  sbox[175U] = (uint8_t)0x1bU;
  sbox[176U] = (uint8_t)0xfcU;
  sbox[177U] = (uint8_t)0x56U;
  sbox[178U] = (uint8_t)0x3eU;
  sbox[179U] = (uint8_t)0x4bU;
  sbox[180U] = (uint8_t)0xc6U;
  sbox[181U] = (uint8_t)0xd2U;
  sbox[182U] = (uint8_t)0x79U;
  sbox[183U] = (uint8_t)0x20U;
  sbox[184U] = (uint8_t)0x9aU;
  sbox[185U] = (uint8_t)0xdbU;
  sbox[186U] = (uint8_t)0xc0U;
  sbox[187U] = (uint8_t)0xfeU;
  sbox[188U] = (uint8_t)0x78U;
  sbox[189U] = (uint8_t)0xcdU;
  sbox[190U] = (uint8_t)0x5aU;
  sbox[191U] = (uint8_t)0xf4U;
  sbox[192U] = (uint8_t)0x1fU;
  sbox[193U] = (uint8_t)0xddU;
  sbox[194U] = (uint8_t)0xa8U;
  sbox[195U] = (uint8_t)0x33U;
  sbox[196U] = (uint8_t)0x88U;
  sbox[197U] = (uint8_t)0x07U;
  sbox[198U] = (uint8_t)0xc7U;
  sbox[199U] = (uint8_t)0x31U;
  sbox[200U] = (uint8_t)0xb1U;
  sbox[201U] = (uint8_t)0x12U;
  sbox[202U] = (uint8_t)0x10U;
  sbox[203U] = (uint8_t)0x59U;
  sbox[204U] = (uint8_t)0x27U;
  sbox[205U] = (uint8_t)0x80U;
  sbox[206U] = (uint8_t)0xecU;
  sbox[207U] = (uint8_t)0x5fU;
  sbox[208U] = (uint8_t)0x60U;
  sbox[209U] = (uint8_t)0x51U;
  sbox[210U] = (uint8_t)0x7fU;
  sbox[211U] = (uint8_t)0xa9U;
  sbox[212U] = (uint8_t)0x19U;
  sbox[213U] = (uint8_t)0xb5U;
  sbox[214U] = (uint8_t)0x4aU;
  sbox[215U] = (uint8_t)0x0dU;
  sbox[216U] = (uint8_t)0x2dU;
  sbox[217U] = (uint8_t)0xe5U;
  sbox[218U] = (uint8_t)0x7aU;
  sbox[219U] = (uint8_t)0x9fU;
  sbox[220U] = (uint8_t)0x93U;
  sbox[221U] = (uint8_t)0xc9U;
  sbox[222U] = (uint8_t)0x9cU;
  sbox[223U] = (uint8_t)0xefU;
  sbox[224U] = (uint8_t)0xa0U;
  sbox[225U] = (uint8_t)0xe0U;
  sbox[226U] = (uint8_t)0x3bU;
  sbox[227U] = (uint8_t)0x4dU;
  sbox[228U] = (uint8_t)0xaeU;
  sbox[229U] = (uint8_t)0x2aU;
  sbox[230U] = (uint8_t)0xf5U;
  sbox[231U] = (uint8_t)0xb0U;
  sbox[232U] = (uint8_t)0xc8U;
  sbox[233U] = (uint8_t)0xebU;
  sbox[234U] = (uint8_t)0xbbU;
  sbox[235U] = (uint8_t)0x3cU;
  sbox[236U] = (uint8_t)0x83U;
  sbox[237U] = (uint8_t)0x53U;
  sbox[238U] = (uint8_t)0x99U;
  sbox[239U] = (uint8_t)0x61U;
  sbox[240U] = (uint8_t)0x17U;
  sbox[241U] = (uint8_t)0x2bU;
  sbox[242U] = (uint8_t)0x04U;
  sbox[243U] = (uint8_t)0x7eU;
  sbox[244U] = (uint8_t)0xbaU;
  sbox[245U] = (uint8_t)0x77U;
  sbox[246U] = (uint8_t)0xd6U;
  sbox[247U] = (uint8_t)0x26U;
  sbox[248U] = (uint8_t)0xe1U;
  sbox[249U] = (uint8_t)0x69U;
  sbox[250U] = (uint8_t)0x14U;
  sbox[251U] = (uint8_t)0x63U;
  sbox[252U] = (uint8_t)0x55U;
  sbox[253U] = (uint8_t)0x21U;
  sbox[254U] = (uint8_t)0x0cU;
  sbox[255U] = (uint8_t)0x7dU;
}

#ifdef _MSC_VER
// Work around a /Ox code-gen bug in AES key expansion, in the MSVC compiler
#pragma optimize("", off)
#pragma optimize("s", on)
#endif

static uint8_t access(uint8_t *sbox, uint8_t i)
{
  return sbox[(uint32_t)i];
}

#ifdef _MSC_VER
#pragma optimize("", on)
#endif

static void subBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr != (uint32_t)16U)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access(sbox, si);
    state[ctr] = si_;
    subBytes_aux_sbox(state, sbox, ctr + (uint32_t)1U);
  }
}

static void subBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  subBytes_aux_sbox(state, sbox, (uint32_t)0U);
}

static void shiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t)1U;
  uint8_t tmp = state[i];
  state[i] = state[i + (uint32_t)4U];
  state[i + (uint32_t)4U] = state[i + (uint32_t)8U];
  state[i + (uint32_t)8U] = state[i + (uint32_t)12U];
  state[i + (uint32_t)12U] = tmp;
  uint32_t i1 = (uint32_t)2U;
  uint8_t tmp1 = state[i1];
  state[i1] = state[i1 + (uint32_t)8U];
  state[i1 + (uint32_t)8U] = tmp1;
  uint8_t tmp2 = state[i1 + (uint32_t)4U];
  state[i1 + (uint32_t)4U] = state[i1 + (uint32_t)12U];
  state[i1 + (uint32_t)12U] = tmp2;
  uint32_t i2 = (uint32_t)3U;
  uint8_t tmp3 = state[i2];
  state[i2] = state[i2 + (uint32_t)12U];
  state[i2 + (uint32_t)12U] = state[i2 + (uint32_t)8U];
  state[i2 + (uint32_t)8U] = state[i2 + (uint32_t)4U];
  state[i2 + (uint32_t)4U] = tmp3;
}

static void mixColumns_(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t)4U * c;
  uint8_t s0 = s[0U];
  uint8_t s1 = s[1U];
  uint8_t s2 = s[2U];
  uint8_t s3 = s[3U];
  s[0U] = multiply((uint8_t)0x2U, s0) ^ (multiply((uint8_t)0x3U, s1) ^ (s2 ^ s3));
  s[1U] = multiply((uint8_t)0x2U, s1) ^ (multiply((uint8_t)0x3U, s2) ^ (s3 ^ s0));
  s[2U] = multiply((uint8_t)0x2U, s2) ^ (multiply((uint8_t)0x3U, s3) ^ (s0 ^ s1));
  s[3U] = multiply((uint8_t)0x2U, s3) ^ (multiply((uint8_t)0x3U, s0) ^ (s1 ^ s2));
}

static void mixColumns(uint8_t *state)
{
  mixColumns_(state, (uint32_t)0U);
  mixColumns_(state, (uint32_t)1U);
  mixColumns_(state, (uint32_t)2U);
  mixColumns_(state, (uint32_t)3U);
}

static void addRoundKey_(uint8_t *state, uint8_t *w, uint32_t round, uint32_t c)
{
  uint8_t *target = state + (uint32_t)4U * c;
  uint8_t *subkey = w + (uint32_t)16U * round + (uint32_t)4U * c;
  target[0U] = target[0U] ^ subkey[0U];
  target[1U] = target[1U] ^ subkey[1U];
  target[2U] = target[2U] ^ subkey[2U];
  target[3U] = target[3U] ^ subkey[3U];
}

static void addRoundKey(uint8_t *state, uint8_t *w, uint32_t round)
{
  addRoundKey_(state, w, round, (uint32_t)0U);
  addRoundKey_(state, w, round, (uint32_t)1U);
  addRoundKey_(state, w, round, (uint32_t)2U);
  addRoundKey_(state, w, round, (uint32_t)3U);
}

static void cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t)14U)
  {
    subBytes_sbox(state, sbox);
    shiftRows(state);
    mixColumns(state);
    addRoundKey(state, w, round);
    cipher_loop(state, w, sbox, round + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (input[0U]));
  addRoundKey(state, w, (uint32_t)0U);
  cipher_loop(state, w, sbox, (uint32_t)1U);
  subBytes_sbox(state, sbox);
  shiftRows(state);
  addRoundKey(state, w, (uint32_t)14U);
  memcpy(out, state, (uint32_t)16U * sizeof (state[0U]));
}

static void rotWord(uint8_t *word)
{
  uint8_t w0 = word[0U];
  uint8_t w1 = word[1U];
  uint8_t w2 = word[2U];
  uint8_t w3 = word[3U];
  word[0U] = w1;
  word[1U] = w2;
  word[2U] = w3;
  word[3U] = w0;
}

static void subWord(uint8_t *word, uint8_t *sbox)
{
  word[0U] = access(sbox, word[0U]);
  word[1U] = access(sbox, word[1U]);
  word[2U] = access(sbox, word[2U]);
  word[3U] = access(sbox, word[3U]);
}

static uint8_t rcon(uint32_t i, uint8_t tmp)
{
  if (i == (uint32_t)1U)
  {
    return tmp;
  }
  else
  {
    uint8_t tmp1 = multiply((uint8_t)0x2U, tmp);
    return rcon(i - (uint32_t)1U, tmp1);
  }
}

static void keyExpansion_aux_0(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  memcpy(temp, w + (uint32_t)4U * j - (uint32_t)4U, (uint32_t)4U * sizeof (w[0U]));
  if (j % (uint32_t)8U == (uint32_t)0U)
  {
    rotWord(temp);
    subWord(temp, sbox);
    uint8_t t0 = temp[0U];
    uint8_t rc = rcon(j / (uint32_t)8U, (uint8_t)1U);
    uint8_t z = t0 ^ rc;
    temp[0U] = z;
  }
  else if (j % (uint32_t)8U == (uint32_t)4U)
  {
    subWord(temp, sbox);
  }
}

static void keyExpansion_aux_1(uint8_t *w, uint8_t *temp, uint32_t j)
{
  uint32_t i = (uint32_t)4U * j;
  uint8_t w0 = w[i + (uint32_t)0U - (uint32_t)32U];
  uint8_t w1 = w[i + (uint32_t)1U - (uint32_t)32U];
  uint8_t w2 = w[i + (uint32_t)2U - (uint32_t)32U];
  uint8_t w3 = w[i + (uint32_t)3U - (uint32_t)32U];
  uint8_t t0 = temp[0U];
  uint8_t t1 = temp[1U];
  uint8_t t2 = temp[2U];
  uint8_t t3 = temp[3U];
  w[i + (uint32_t)0U] = t0 ^ w0;
  w[i + (uint32_t)1U] = t1 ^ w1;
  w[i + (uint32_t)2U] = t2 ^ w2;
  w[i + (uint32_t)3U] = t3 ^ w3;
}

static void keyExpansion_aux(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  if (j < (uint32_t)60U)
  {
    keyExpansion_aux_0(w, temp, sbox, j);
    keyExpansion_aux_1(w, temp, j);
    keyExpansion_aux(w, temp, sbox, j + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox)
{
  uint8_t temp[4U] = { 0U };
  memcpy(w, key, (uint32_t)32U * sizeof (key[0U]));
  keyExpansion_aux(w, temp, sbox, (uint32_t)8U);
}

static void invSubBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (!(ctr == (uint32_t)16U))
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access(sbox, si);
    state[ctr] = si_;
    invSubBytes_aux_sbox(state, sbox, ctr + (uint32_t)1U);
  }
}

static void invSubBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  invSubBytes_aux_sbox(state, sbox, (uint32_t)0U);
}

static void invShiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t)3U;
  uint8_t tmp = state[i];
  state[i] = state[i + (uint32_t)4U];
  state[i + (uint32_t)4U] = state[i + (uint32_t)8U];
  state[i + (uint32_t)8U] = state[i + (uint32_t)12U];
  state[i + (uint32_t)12U] = tmp;
  uint32_t i1 = (uint32_t)2U;
  uint8_t tmp1 = state[i1];
  state[i1] = state[i1 + (uint32_t)8U];
  state[i1 + (uint32_t)8U] = tmp1;
  uint8_t tmp2 = state[i1 + (uint32_t)4U];
  state[i1 + (uint32_t)4U] = state[i1 + (uint32_t)12U];
  state[i1 + (uint32_t)12U] = tmp2;
  uint32_t i2 = (uint32_t)1U;
  uint8_t tmp3 = state[i2];
  state[i2] = state[i2 + (uint32_t)12U];
  state[i2 + (uint32_t)12U] = state[i2 + (uint32_t)8U];
  state[i2 + (uint32_t)8U] = state[i2 + (uint32_t)4U];
  state[i2 + (uint32_t)4U] = tmp3;
}

static void invMixColumns_(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t)4U * c;
  uint8_t s0 = s[0U];
  uint8_t s1 = s[1U];
  uint8_t s2 = s[2U];
  uint8_t s3 = s[3U];
  s[0U] =
    multiply((uint8_t)0xeU,
      s0)
    ^ (multiply((uint8_t)0xbU, s1) ^ (multiply((uint8_t)0xdU, s2) ^ multiply((uint8_t)0x9U, s3)));
  s[1U] =
    multiply((uint8_t)0xeU,
      s1)
    ^ (multiply((uint8_t)0xbU, s2) ^ (multiply((uint8_t)0xdU, s3) ^ multiply((uint8_t)0x9U, s0)));
  s[2U] =
    multiply((uint8_t)0xeU,
      s2)
    ^ (multiply((uint8_t)0xbU, s3) ^ (multiply((uint8_t)0xdU, s0) ^ multiply((uint8_t)0x9U, s1)));
  s[3U] =
    multiply((uint8_t)0xeU,
      s3)
    ^ (multiply((uint8_t)0xbU, s0) ^ (multiply((uint8_t)0xdU, s1) ^ multiply((uint8_t)0x9U, s2)));
}

static void invMixColumns(uint8_t *state)
{
  invMixColumns_(state, (uint32_t)0U);
  invMixColumns_(state, (uint32_t)1U);
  invMixColumns_(state, (uint32_t)2U);
  invMixColumns_(state, (uint32_t)3U);
}

static void inv_cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t)0U)
  {
    invShiftRows(state);
    invSubBytes_sbox(state, sbox);
    addRoundKey(state, w, round);
    invMixColumns(state);
    inv_cipher_loop(state, w, sbox, round - (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (input[0U]));
  addRoundKey(state, w, (uint32_t)14U);
  inv_cipher_loop(state, w, sbox, (uint32_t)13U);
  invShiftRows(state);
  invSubBytes_sbox(state, sbox);
  addRoundKey(state, w, (uint32_t)0U);
  memcpy(out, state, (uint32_t)16U * sizeof (state[0U]));
}

static uint8_t multiply0(uint8_t a, uint8_t b)
{
  return
    a
    * (b & (uint8_t)1U)
    ^
      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
      * (b >> (uint32_t)1U & (uint8_t)1U)
      ^
        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
        << (uint32_t)1U
        ^
          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
          >> (uint32_t)7U
          & (uint8_t)1U)
          * (uint8_t)0x1bU)
        * (b >> (uint32_t)2U & (uint8_t)1U)
        ^
          ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
          << (uint32_t)1U
          ^
            ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            >> (uint32_t)7U
            & (uint8_t)1U)
            * (uint8_t)0x1bU)
          << (uint32_t)1U
          ^
            (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            >> (uint32_t)7U
            & (uint8_t)1U)
            * (uint8_t)0x1bU)
          * (b >> (uint32_t)3U & (uint8_t)1U)
          ^
            (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            << (uint32_t)1U
            ^
              ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              >> (uint32_t)7U
              & (uint8_t)1U)
              * (uint8_t)0x1bU)
            * (b >> (uint32_t)4U & (uint8_t)1U)
            ^
              ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              << (uint32_t)1U
              ^
                (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                >> (uint32_t)7U
                & (uint8_t)1U)
                * (uint8_t)0x1bU)
              * (b >> (uint32_t)5U & (uint8_t)1U)
              ^
                (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                << (uint32_t)1U
                ^
                  ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  >> (uint32_t)7U
                  & (uint8_t)1U)
                  * (uint8_t)0x1bU)
                * (b >> (uint32_t)6U & (uint8_t)1U)
                ^
                  (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  << (uint32_t)1U
                  ^
                    (((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    << (uint32_t)1U
                    ^
                      ((((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        ((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      << (uint32_t)1U
                      ^
                        (((((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          (((a << (uint32_t)1U ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        << (uint32_t)1U
                        ^
                          ((((a
                          << (uint32_t)1U
                          ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            ((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          << (uint32_t)1U
                          ^
                            (((a
                            << (uint32_t)1U
                            ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                            << (uint32_t)1U
                            ^
                              ((a
                              << (uint32_t)1U
                              ^ (a >> (uint32_t)7U & (uint8_t)1U) * (uint8_t)0x1bU)
                              >> (uint32_t)7U
                              & (uint8_t)1U)
                              * (uint8_t)0x1bU)
                            >> (uint32_t)7U
                            & (uint8_t)1U)
                            * (uint8_t)0x1bU)
                          >> (uint32_t)7U
                          & (uint8_t)1U)
                          * (uint8_t)0x1bU)
                        >> (uint32_t)7U
                        & (uint8_t)1U)
                        * (uint8_t)0x1bU)
                      >> (uint32_t)7U
                      & (uint8_t)1U)
                      * (uint8_t)0x1bU)
                    >> (uint32_t)7U
                    & (uint8_t)1U)
                    * (uint8_t)0x1bU)
                  * (b >> (uint32_t)7U & (uint8_t)1U)))))));
}

void Crypto_Symmetric_AES128_mk_sbox(uint8_t *sbox)
{
  sbox[0U] = (uint8_t)0x63U;
  sbox[1U] = (uint8_t)0x7cU;
  sbox[2U] = (uint8_t)0x77U;
  sbox[3U] = (uint8_t)0x7bU;
  sbox[4U] = (uint8_t)0xf2U;
  sbox[5U] = (uint8_t)0x6bU;
  sbox[6U] = (uint8_t)0x6fU;
  sbox[7U] = (uint8_t)0xc5U;
  sbox[8U] = (uint8_t)0x30U;
  sbox[9U] = (uint8_t)0x01U;
  sbox[10U] = (uint8_t)0x67U;
  sbox[11U] = (uint8_t)0x2bU;
  sbox[12U] = (uint8_t)0xfeU;
  sbox[13U] = (uint8_t)0xd7U;
  sbox[14U] = (uint8_t)0xabU;
  sbox[15U] = (uint8_t)0x76U;
  sbox[16U] = (uint8_t)0xcaU;
  sbox[17U] = (uint8_t)0x82U;
  sbox[18U] = (uint8_t)0xc9U;
  sbox[19U] = (uint8_t)0x7dU;
  sbox[20U] = (uint8_t)0xfaU;
  sbox[21U] = (uint8_t)0x59U;
  sbox[22U] = (uint8_t)0x47U;
  sbox[23U] = (uint8_t)0xf0U;
  sbox[24U] = (uint8_t)0xadU;
  sbox[25U] = (uint8_t)0xd4U;
  sbox[26U] = (uint8_t)0xa2U;
  sbox[27U] = (uint8_t)0xafU;
  sbox[28U] = (uint8_t)0x9cU;
  sbox[29U] = (uint8_t)0xa4U;
  sbox[30U] = (uint8_t)0x72U;
  sbox[31U] = (uint8_t)0xc0U;
  sbox[32U] = (uint8_t)0xb7U;
  sbox[33U] = (uint8_t)0xfdU;
  sbox[34U] = (uint8_t)0x93U;
  sbox[35U] = (uint8_t)0x26U;
  sbox[36U] = (uint8_t)0x36U;
  sbox[37U] = (uint8_t)0x3fU;
  sbox[38U] = (uint8_t)0xf7U;
  sbox[39U] = (uint8_t)0xccU;
  sbox[40U] = (uint8_t)0x34U;
  sbox[41U] = (uint8_t)0xa5U;
  sbox[42U] = (uint8_t)0xe5U;
  sbox[43U] = (uint8_t)0xf1U;
  sbox[44U] = (uint8_t)0x71U;
  sbox[45U] = (uint8_t)0xd8U;
  sbox[46U] = (uint8_t)0x31U;
  sbox[47U] = (uint8_t)0x15U;
  sbox[48U] = (uint8_t)0x04U;
  sbox[49U] = (uint8_t)0xc7U;
  sbox[50U] = (uint8_t)0x23U;
  sbox[51U] = (uint8_t)0xc3U;
  sbox[52U] = (uint8_t)0x18U;
  sbox[53U] = (uint8_t)0x96U;
  sbox[54U] = (uint8_t)0x05U;
  sbox[55U] = (uint8_t)0x9aU;
  sbox[56U] = (uint8_t)0x07U;
  sbox[57U] = (uint8_t)0x12U;
  sbox[58U] = (uint8_t)0x80U;
  sbox[59U] = (uint8_t)0xe2U;
  sbox[60U] = (uint8_t)0xebU;
  sbox[61U] = (uint8_t)0x27U;
  sbox[62U] = (uint8_t)0xb2U;
  sbox[63U] = (uint8_t)0x75U;
  sbox[64U] = (uint8_t)0x09U;
  sbox[65U] = (uint8_t)0x83U;
  sbox[66U] = (uint8_t)0x2cU;
  sbox[67U] = (uint8_t)0x1aU;
  sbox[68U] = (uint8_t)0x1bU;
  sbox[69U] = (uint8_t)0x6eU;
  sbox[70U] = (uint8_t)0x5aU;
  sbox[71U] = (uint8_t)0xa0U;
  sbox[72U] = (uint8_t)0x52U;
  sbox[73U] = (uint8_t)0x3bU;
  sbox[74U] = (uint8_t)0xd6U;
  sbox[75U] = (uint8_t)0xb3U;
  sbox[76U] = (uint8_t)0x29U;
  sbox[77U] = (uint8_t)0xe3U;
  sbox[78U] = (uint8_t)0x2fU;
  sbox[79U] = (uint8_t)0x84U;
  sbox[80U] = (uint8_t)0x53U;
  sbox[81U] = (uint8_t)0xd1U;
  sbox[82U] = (uint8_t)0x00U;
  sbox[83U] = (uint8_t)0xedU;
  sbox[84U] = (uint8_t)0x20U;
  sbox[85U] = (uint8_t)0xfcU;
  sbox[86U] = (uint8_t)0xb1U;
  sbox[87U] = (uint8_t)0x5bU;
  sbox[88U] = (uint8_t)0x6aU;
  sbox[89U] = (uint8_t)0xcbU;
  sbox[90U] = (uint8_t)0xbeU;
  sbox[91U] = (uint8_t)0x39U;
  sbox[92U] = (uint8_t)0x4aU;
  sbox[93U] = (uint8_t)0x4cU;
  sbox[94U] = (uint8_t)0x58U;
  sbox[95U] = (uint8_t)0xcfU;
  sbox[96U] = (uint8_t)0xd0U;
  sbox[97U] = (uint8_t)0xefU;
  sbox[98U] = (uint8_t)0xaaU;
  sbox[99U] = (uint8_t)0xfbU;
  sbox[100U] = (uint8_t)0x43U;
  sbox[101U] = (uint8_t)0x4dU;
  sbox[102U] = (uint8_t)0x33U;
  sbox[103U] = (uint8_t)0x85U;
  sbox[104U] = (uint8_t)0x45U;
  sbox[105U] = (uint8_t)0xf9U;
  sbox[106U] = (uint8_t)0x02U;
  sbox[107U] = (uint8_t)0x7fU;
  sbox[108U] = (uint8_t)0x50U;
  sbox[109U] = (uint8_t)0x3cU;
  sbox[110U] = (uint8_t)0x9fU;
  sbox[111U] = (uint8_t)0xa8U;
  sbox[112U] = (uint8_t)0x51U;
  sbox[113U] = (uint8_t)0xa3U;
  sbox[114U] = (uint8_t)0x40U;
  sbox[115U] = (uint8_t)0x8fU;
  sbox[116U] = (uint8_t)0x92U;
  sbox[117U] = (uint8_t)0x9dU;
  sbox[118U] = (uint8_t)0x38U;
  sbox[119U] = (uint8_t)0xf5U;
  sbox[120U] = (uint8_t)0xbcU;
  sbox[121U] = (uint8_t)0xb6U;
  sbox[122U] = (uint8_t)0xdaU;
  sbox[123U] = (uint8_t)0x21U;
  sbox[124U] = (uint8_t)0x10U;
  sbox[125U] = (uint8_t)0xffU;
  sbox[126U] = (uint8_t)0xf3U;
  sbox[127U] = (uint8_t)0xd2U;
  sbox[128U] = (uint8_t)0xcdU;
  sbox[129U] = (uint8_t)0x0cU;
  sbox[130U] = (uint8_t)0x13U;
  sbox[131U] = (uint8_t)0xecU;
  sbox[132U] = (uint8_t)0x5fU;
  sbox[133U] = (uint8_t)0x97U;
  sbox[134U] = (uint8_t)0x44U;
  sbox[135U] = (uint8_t)0x17U;
  sbox[136U] = (uint8_t)0xc4U;
  sbox[137U] = (uint8_t)0xa7U;
  sbox[138U] = (uint8_t)0x7eU;
  sbox[139U] = (uint8_t)0x3dU;
  sbox[140U] = (uint8_t)0x64U;
  sbox[141U] = (uint8_t)0x5dU;
  sbox[142U] = (uint8_t)0x19U;
  sbox[143U] = (uint8_t)0x73U;
  sbox[144U] = (uint8_t)0x60U;
  sbox[145U] = (uint8_t)0x81U;
  sbox[146U] = (uint8_t)0x4fU;
  sbox[147U] = (uint8_t)0xdcU;
  sbox[148U] = (uint8_t)0x22U;
  sbox[149U] = (uint8_t)0x2aU;
  sbox[150U] = (uint8_t)0x90U;
  sbox[151U] = (uint8_t)0x88U;
  sbox[152U] = (uint8_t)0x46U;
  sbox[153U] = (uint8_t)0xeeU;
  sbox[154U] = (uint8_t)0xb8U;
  sbox[155U] = (uint8_t)0x14U;
  sbox[156U] = (uint8_t)0xdeU;
  sbox[157U] = (uint8_t)0x5eU;
  sbox[158U] = (uint8_t)0x0bU;
  sbox[159U] = (uint8_t)0xdbU;
  sbox[160U] = (uint8_t)0xe0U;
  sbox[161U] = (uint8_t)0x32U;
  sbox[162U] = (uint8_t)0x3aU;
  sbox[163U] = (uint8_t)0x0aU;
  sbox[164U] = (uint8_t)0x49U;
  sbox[165U] = (uint8_t)0x06U;
  sbox[166U] = (uint8_t)0x24U;
  sbox[167U] = (uint8_t)0x5cU;
  sbox[168U] = (uint8_t)0xc2U;
  sbox[169U] = (uint8_t)0xd3U;
  sbox[170U] = (uint8_t)0xacU;
  sbox[171U] = (uint8_t)0x62U;
  sbox[172U] = (uint8_t)0x91U;
  sbox[173U] = (uint8_t)0x95U;
  sbox[174U] = (uint8_t)0xe4U;
  sbox[175U] = (uint8_t)0x79U;
  sbox[176U] = (uint8_t)0xe7U;
  sbox[177U] = (uint8_t)0xc8U;
  sbox[178U] = (uint8_t)0x37U;
  sbox[179U] = (uint8_t)0x6dU;
  sbox[180U] = (uint8_t)0x8dU;
  sbox[181U] = (uint8_t)0xd5U;
  sbox[182U] = (uint8_t)0x4eU;
  sbox[183U] = (uint8_t)0xa9U;
  sbox[184U] = (uint8_t)0x6cU;
  sbox[185U] = (uint8_t)0x56U;
  sbox[186U] = (uint8_t)0xf4U;
  sbox[187U] = (uint8_t)0xeaU;
  sbox[188U] = (uint8_t)0x65U;
  sbox[189U] = (uint8_t)0x7aU;
  sbox[190U] = (uint8_t)0xaeU;
  sbox[191U] = (uint8_t)0x08U;
  sbox[192U] = (uint8_t)0xbaU;
  sbox[193U] = (uint8_t)0x78U;
  sbox[194U] = (uint8_t)0x25U;
  sbox[195U] = (uint8_t)0x2eU;
  sbox[196U] = (uint8_t)0x1cU;
  sbox[197U] = (uint8_t)0xa6U;
  sbox[198U] = (uint8_t)0xb4U;
  sbox[199U] = (uint8_t)0xc6U;
  sbox[200U] = (uint8_t)0xe8U;
  sbox[201U] = (uint8_t)0xddU;
  sbox[202U] = (uint8_t)0x74U;
  sbox[203U] = (uint8_t)0x1fU;
  sbox[204U] = (uint8_t)0x4bU;
  sbox[205U] = (uint8_t)0xbdU;
  sbox[206U] = (uint8_t)0x8bU;
  sbox[207U] = (uint8_t)0x8aU;
  sbox[208U] = (uint8_t)0x70U;
  sbox[209U] = (uint8_t)0x3eU;
  sbox[210U] = (uint8_t)0xb5U;
  sbox[211U] = (uint8_t)0x66U;
  sbox[212U] = (uint8_t)0x48U;
  sbox[213U] = (uint8_t)0x03U;
  sbox[214U] = (uint8_t)0xf6U;
  sbox[215U] = (uint8_t)0x0eU;
  sbox[216U] = (uint8_t)0x61U;
  sbox[217U] = (uint8_t)0x35U;
  sbox[218U] = (uint8_t)0x57U;
  sbox[219U] = (uint8_t)0xb9U;
  sbox[220U] = (uint8_t)0x86U;
  sbox[221U] = (uint8_t)0xc1U;
  sbox[222U] = (uint8_t)0x1dU;
  sbox[223U] = (uint8_t)0x9eU;
  sbox[224U] = (uint8_t)0xe1U;
  sbox[225U] = (uint8_t)0xf8U;
  sbox[226U] = (uint8_t)0x98U;
  sbox[227U] = (uint8_t)0x11U;
  sbox[228U] = (uint8_t)0x69U;
  sbox[229U] = (uint8_t)0xd9U;
  sbox[230U] = (uint8_t)0x8eU;
  sbox[231U] = (uint8_t)0x94U;
  sbox[232U] = (uint8_t)0x9bU;
  sbox[233U] = (uint8_t)0x1eU;
  sbox[234U] = (uint8_t)0x87U;
  sbox[235U] = (uint8_t)0xe9U;
  sbox[236U] = (uint8_t)0xceU;
  sbox[237U] = (uint8_t)0x55U;
  sbox[238U] = (uint8_t)0x28U;
  sbox[239U] = (uint8_t)0xdfU;
  sbox[240U] = (uint8_t)0x8cU;
  sbox[241U] = (uint8_t)0xa1U;
  sbox[242U] = (uint8_t)0x89U;
  sbox[243U] = (uint8_t)0x0dU;
  sbox[244U] = (uint8_t)0xbfU;
  sbox[245U] = (uint8_t)0xe6U;
  sbox[246U] = (uint8_t)0x42U;
  sbox[247U] = (uint8_t)0x68U;
  sbox[248U] = (uint8_t)0x41U;
  sbox[249U] = (uint8_t)0x99U;
  sbox[250U] = (uint8_t)0x2dU;
  sbox[251U] = (uint8_t)0x0fU;
  sbox[252U] = (uint8_t)0xb0U;
  sbox[253U] = (uint8_t)0x54U;
  sbox[254U] = (uint8_t)0xbbU;
  sbox[255U] = (uint8_t)0x16U;
}

void Crypto_Symmetric_AES128_mk_inv_sbox(uint8_t *sbox)
{
  sbox[0U] = (uint8_t)0x52U;
  sbox[1U] = (uint8_t)0x09U;
  sbox[2U] = (uint8_t)0x6aU;
  sbox[3U] = (uint8_t)0xd5U;
  sbox[4U] = (uint8_t)0x30U;
  sbox[5U] = (uint8_t)0x36U;
  sbox[6U] = (uint8_t)0xa5U;
  sbox[7U] = (uint8_t)0x38U;
  sbox[8U] = (uint8_t)0xbfU;
  sbox[9U] = (uint8_t)0x40U;
  sbox[10U] = (uint8_t)0xa3U;
  sbox[11U] = (uint8_t)0x9eU;
  sbox[12U] = (uint8_t)0x81U;
  sbox[13U] = (uint8_t)0xf3U;
  sbox[14U] = (uint8_t)0xd7U;
  sbox[15U] = (uint8_t)0xfbU;
  sbox[16U] = (uint8_t)0x7cU;
  sbox[17U] = (uint8_t)0xe3U;
  sbox[18U] = (uint8_t)0x39U;
  sbox[19U] = (uint8_t)0x82U;
  sbox[20U] = (uint8_t)0x9bU;
  sbox[21U] = (uint8_t)0x2fU;
  sbox[22U] = (uint8_t)0xffU;
  sbox[23U] = (uint8_t)0x87U;
  sbox[24U] = (uint8_t)0x34U;
  sbox[25U] = (uint8_t)0x8eU;
  sbox[26U] = (uint8_t)0x43U;
  sbox[27U] = (uint8_t)0x44U;
  sbox[28U] = (uint8_t)0xc4U;
  sbox[29U] = (uint8_t)0xdeU;
  sbox[30U] = (uint8_t)0xe9U;
  sbox[31U] = (uint8_t)0xcbU;
  sbox[32U] = (uint8_t)0x54U;
  sbox[33U] = (uint8_t)0x7bU;
  sbox[34U] = (uint8_t)0x94U;
  sbox[35U] = (uint8_t)0x32U;
  sbox[36U] = (uint8_t)0xa6U;
  sbox[37U] = (uint8_t)0xc2U;
  sbox[38U] = (uint8_t)0x23U;
  sbox[39U] = (uint8_t)0x3dU;
  sbox[40U] = (uint8_t)0xeeU;
  sbox[41U] = (uint8_t)0x4cU;
  sbox[42U] = (uint8_t)0x95U;
  sbox[43U] = (uint8_t)0x0bU;
  sbox[44U] = (uint8_t)0x42U;
  sbox[45U] = (uint8_t)0xfaU;
  sbox[46U] = (uint8_t)0xc3U;
  sbox[47U] = (uint8_t)0x4eU;
  sbox[48U] = (uint8_t)0x08U;
  sbox[49U] = (uint8_t)0x2eU;
  sbox[50U] = (uint8_t)0xa1U;
  sbox[51U] = (uint8_t)0x66U;
  sbox[52U] = (uint8_t)0x28U;
  sbox[53U] = (uint8_t)0xd9U;
  sbox[54U] = (uint8_t)0x24U;
  sbox[55U] = (uint8_t)0xb2U;
  sbox[56U] = (uint8_t)0x76U;
  sbox[57U] = (uint8_t)0x5bU;
  sbox[58U] = (uint8_t)0xa2U;
  sbox[59U] = (uint8_t)0x49U;
  sbox[60U] = (uint8_t)0x6dU;
  sbox[61U] = (uint8_t)0x8bU;
  sbox[62U] = (uint8_t)0xd1U;
  sbox[63U] = (uint8_t)0x25U;
  sbox[64U] = (uint8_t)0x72U;
  sbox[65U] = (uint8_t)0xf8U;
  sbox[66U] = (uint8_t)0xf6U;
  sbox[67U] = (uint8_t)0x64U;
  sbox[68U] = (uint8_t)0x86U;
  sbox[69U] = (uint8_t)0x68U;
  sbox[70U] = (uint8_t)0x98U;
  sbox[71U] = (uint8_t)0x16U;
  sbox[72U] = (uint8_t)0xd4U;
  sbox[73U] = (uint8_t)0xa4U;
  sbox[74U] = (uint8_t)0x5cU;
  sbox[75U] = (uint8_t)0xccU;
  sbox[76U] = (uint8_t)0x5dU;
  sbox[77U] = (uint8_t)0x65U;
  sbox[78U] = (uint8_t)0xb6U;
  sbox[79U] = (uint8_t)0x92U;
  sbox[80U] = (uint8_t)0x6cU;
  sbox[81U] = (uint8_t)0x70U;
  sbox[82U] = (uint8_t)0x48U;
  sbox[83U] = (uint8_t)0x50U;
  sbox[84U] = (uint8_t)0xfdU;
  sbox[85U] = (uint8_t)0xedU;
  sbox[86U] = (uint8_t)0xb9U;
  sbox[87U] = (uint8_t)0xdaU;
  sbox[88U] = (uint8_t)0x5eU;
  sbox[89U] = (uint8_t)0x15U;
  sbox[90U] = (uint8_t)0x46U;
  sbox[91U] = (uint8_t)0x57U;
  sbox[92U] = (uint8_t)0xa7U;
  sbox[93U] = (uint8_t)0x8dU;
  sbox[94U] = (uint8_t)0x9dU;
  sbox[95U] = (uint8_t)0x84U;
  sbox[96U] = (uint8_t)0x90U;
  sbox[97U] = (uint8_t)0xd8U;
  sbox[98U] = (uint8_t)0xabU;
  sbox[99U] = (uint8_t)0x00U;
  sbox[100U] = (uint8_t)0x8cU;
  sbox[101U] = (uint8_t)0xbcU;
  sbox[102U] = (uint8_t)0xd3U;
  sbox[103U] = (uint8_t)0x0aU;
  sbox[104U] = (uint8_t)0xf7U;
  sbox[105U] = (uint8_t)0xe4U;
  sbox[106U] = (uint8_t)0x58U;
  sbox[107U] = (uint8_t)0x05U;
  sbox[108U] = (uint8_t)0xb8U;
  sbox[109U] = (uint8_t)0xb3U;
  sbox[110U] = (uint8_t)0x45U;
  sbox[111U] = (uint8_t)0x06U;
  sbox[112U] = (uint8_t)0xd0U;
  sbox[113U] = (uint8_t)0x2cU;
  sbox[114U] = (uint8_t)0x1eU;
  sbox[115U] = (uint8_t)0x8fU;
  sbox[116U] = (uint8_t)0xcaU;
  sbox[117U] = (uint8_t)0x3fU;
  sbox[118U] = (uint8_t)0x0fU;
  sbox[119U] = (uint8_t)0x02U;
  sbox[120U] = (uint8_t)0xc1U;
  sbox[121U] = (uint8_t)0xafU;
  sbox[122U] = (uint8_t)0xbdU;
  sbox[123U] = (uint8_t)0x03U;
  sbox[124U] = (uint8_t)0x01U;
  sbox[125U] = (uint8_t)0x13U;
  sbox[126U] = (uint8_t)0x8aU;
  sbox[127U] = (uint8_t)0x6bU;
  sbox[128U] = (uint8_t)0x3aU;
  sbox[129U] = (uint8_t)0x91U;
  sbox[130U] = (uint8_t)0x11U;
  sbox[131U] = (uint8_t)0x41U;
  sbox[132U] = (uint8_t)0x4fU;
  sbox[133U] = (uint8_t)0x67U;
  sbox[134U] = (uint8_t)0xdcU;
  sbox[135U] = (uint8_t)0xeaU;
  sbox[136U] = (uint8_t)0x97U;
  sbox[137U] = (uint8_t)0xf2U;
  sbox[138U] = (uint8_t)0xcfU;
  sbox[139U] = (uint8_t)0xceU;
  sbox[140U] = (uint8_t)0xf0U;
  sbox[141U] = (uint8_t)0xb4U;
  sbox[142U] = (uint8_t)0xe6U;
  sbox[143U] = (uint8_t)0x73U;
  sbox[144U] = (uint8_t)0x96U;
  sbox[145U] = (uint8_t)0xacU;
  sbox[146U] = (uint8_t)0x74U;
  sbox[147U] = (uint8_t)0x22U;
  sbox[148U] = (uint8_t)0xe7U;
  sbox[149U] = (uint8_t)0xadU;
  sbox[150U] = (uint8_t)0x35U;
  sbox[151U] = (uint8_t)0x85U;
  sbox[152U] = (uint8_t)0xe2U;
  sbox[153U] = (uint8_t)0xf9U;
  sbox[154U] = (uint8_t)0x37U;
  sbox[155U] = (uint8_t)0xe8U;
  sbox[156U] = (uint8_t)0x1cU;
  sbox[157U] = (uint8_t)0x75U;
  sbox[158U] = (uint8_t)0xdfU;
  sbox[159U] = (uint8_t)0x6eU;
  sbox[160U] = (uint8_t)0x47U;
  sbox[161U] = (uint8_t)0xf1U;
  sbox[162U] = (uint8_t)0x1aU;
  sbox[163U] = (uint8_t)0x71U;
  sbox[164U] = (uint8_t)0x1dU;
  sbox[165U] = (uint8_t)0x29U;
  sbox[166U] = (uint8_t)0xc5U;
  sbox[167U] = (uint8_t)0x89U;
  sbox[168U] = (uint8_t)0x6fU;
  sbox[169U] = (uint8_t)0xb7U;
  sbox[170U] = (uint8_t)0x62U;
  sbox[171U] = (uint8_t)0x0eU;
  sbox[172U] = (uint8_t)0xaaU;
  sbox[173U] = (uint8_t)0x18U;
  sbox[174U] = (uint8_t)0xbeU;
  sbox[175U] = (uint8_t)0x1bU;
  sbox[176U] = (uint8_t)0xfcU;
  sbox[177U] = (uint8_t)0x56U;
  sbox[178U] = (uint8_t)0x3eU;
  sbox[179U] = (uint8_t)0x4bU;
  sbox[180U] = (uint8_t)0xc6U;
  sbox[181U] = (uint8_t)0xd2U;
  sbox[182U] = (uint8_t)0x79U;
  sbox[183U] = (uint8_t)0x20U;
  sbox[184U] = (uint8_t)0x9aU;
  sbox[185U] = (uint8_t)0xdbU;
  sbox[186U] = (uint8_t)0xc0U;
  sbox[187U] = (uint8_t)0xfeU;
  sbox[188U] = (uint8_t)0x78U;
  sbox[189U] = (uint8_t)0xcdU;
  sbox[190U] = (uint8_t)0x5aU;
  sbox[191U] = (uint8_t)0xf4U;
  sbox[192U] = (uint8_t)0x1fU;
  sbox[193U] = (uint8_t)0xddU;
  sbox[194U] = (uint8_t)0xa8U;
  sbox[195U] = (uint8_t)0x33U;
  sbox[196U] = (uint8_t)0x88U;
  sbox[197U] = (uint8_t)0x07U;
  sbox[198U] = (uint8_t)0xc7U;
  sbox[199U] = (uint8_t)0x31U;
  sbox[200U] = (uint8_t)0xb1U;
  sbox[201U] = (uint8_t)0x12U;
  sbox[202U] = (uint8_t)0x10U;
  sbox[203U] = (uint8_t)0x59U;
  sbox[204U] = (uint8_t)0x27U;
  sbox[205U] = (uint8_t)0x80U;
  sbox[206U] = (uint8_t)0xecU;
  sbox[207U] = (uint8_t)0x5fU;
  sbox[208U] = (uint8_t)0x60U;
  sbox[209U] = (uint8_t)0x51U;
  sbox[210U] = (uint8_t)0x7fU;
  sbox[211U] = (uint8_t)0xa9U;
  sbox[212U] = (uint8_t)0x19U;
  sbox[213U] = (uint8_t)0xb5U;
  sbox[214U] = (uint8_t)0x4aU;
  sbox[215U] = (uint8_t)0x0dU;
  sbox[216U] = (uint8_t)0x2dU;
  sbox[217U] = (uint8_t)0xe5U;
  sbox[218U] = (uint8_t)0x7aU;
  sbox[219U] = (uint8_t)0x9fU;
  sbox[220U] = (uint8_t)0x93U;
  sbox[221U] = (uint8_t)0xc9U;
  sbox[222U] = (uint8_t)0x9cU;
  sbox[223U] = (uint8_t)0xefU;
  sbox[224U] = (uint8_t)0xa0U;
  sbox[225U] = (uint8_t)0xe0U;
  sbox[226U] = (uint8_t)0x3bU;
  sbox[227U] = (uint8_t)0x4dU;
  sbox[228U] = (uint8_t)0xaeU;
  sbox[229U] = (uint8_t)0x2aU;
  sbox[230U] = (uint8_t)0xf5U;
  sbox[231U] = (uint8_t)0xb0U;
  sbox[232U] = (uint8_t)0xc8U;
  sbox[233U] = (uint8_t)0xebU;
  sbox[234U] = (uint8_t)0xbbU;
  sbox[235U] = (uint8_t)0x3cU;
  sbox[236U] = (uint8_t)0x83U;
  sbox[237U] = (uint8_t)0x53U;
  sbox[238U] = (uint8_t)0x99U;
  sbox[239U] = (uint8_t)0x61U;
  sbox[240U] = (uint8_t)0x17U;
  sbox[241U] = (uint8_t)0x2bU;
  sbox[242U] = (uint8_t)0x04U;
  sbox[243U] = (uint8_t)0x7eU;
  sbox[244U] = (uint8_t)0xbaU;
  sbox[245U] = (uint8_t)0x77U;
  sbox[246U] = (uint8_t)0xd6U;
  sbox[247U] = (uint8_t)0x26U;
  sbox[248U] = (uint8_t)0xe1U;
  sbox[249U] = (uint8_t)0x69U;
  sbox[250U] = (uint8_t)0x14U;
  sbox[251U] = (uint8_t)0x63U;
  sbox[252U] = (uint8_t)0x55U;
  sbox[253U] = (uint8_t)0x21U;
  sbox[254U] = (uint8_t)0x0cU;
  sbox[255U] = (uint8_t)0x7dU;
}

#ifdef _MSC_VER
// Work around a /Ox code-gen bug in AES key expansion, in the MSVC compiler
#pragma optimize("", off)
#pragma optimize("s", on)
#endif

static uint8_t access0(uint8_t *sbox, uint8_t i)
{
  return sbox[(uint32_t)i];
}

#ifdef _MSC_VER
#pragma optimize("", on)
#endif

static void subBytes_aux_sbox0(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr != (uint32_t)16U)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access0(sbox, si);
    state[ctr] = si_;
    subBytes_aux_sbox0(state, sbox, ctr + (uint32_t)1U);
  }
}

static void subBytes_sbox0(uint8_t *state, uint8_t *sbox)
{
  subBytes_aux_sbox0(state, sbox, (uint32_t)0U);
}

static void shiftRows0(uint8_t *state)
{
  uint32_t i = (uint32_t)1U;
  uint8_t tmp = state[i];
  state[i] = state[i + (uint32_t)4U];
  state[i + (uint32_t)4U] = state[i + (uint32_t)8U];
  state[i + (uint32_t)8U] = state[i + (uint32_t)12U];
  state[i + (uint32_t)12U] = tmp;
  uint32_t i1 = (uint32_t)2U;
  uint8_t tmp1 = state[i1];
  state[i1] = state[i1 + (uint32_t)8U];
  state[i1 + (uint32_t)8U] = tmp1;
  uint8_t tmp2 = state[i1 + (uint32_t)4U];
  state[i1 + (uint32_t)4U] = state[i1 + (uint32_t)12U];
  state[i1 + (uint32_t)12U] = tmp2;
  uint32_t i2 = (uint32_t)3U;
  uint8_t tmp3 = state[i2];
  state[i2] = state[i2 + (uint32_t)12U];
  state[i2 + (uint32_t)12U] = state[i2 + (uint32_t)8U];
  state[i2 + (uint32_t)8U] = state[i2 + (uint32_t)4U];
  state[i2 + (uint32_t)4U] = tmp3;
}

static void mixColumns_0(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t)4U * c;
  uint8_t s0 = s[0U];
  uint8_t s1 = s[1U];
  uint8_t s2 = s[2U];
  uint8_t s3 = s[3U];
  s[0U] = multiply0((uint8_t)0x2U, s0) ^ (multiply0((uint8_t)0x3U, s1) ^ (s2 ^ s3));
  s[1U] = multiply0((uint8_t)0x2U, s1) ^ (multiply0((uint8_t)0x3U, s2) ^ (s3 ^ s0));
  s[2U] = multiply0((uint8_t)0x2U, s2) ^ (multiply0((uint8_t)0x3U, s3) ^ (s0 ^ s1));
  s[3U] = multiply0((uint8_t)0x2U, s3) ^ (multiply0((uint8_t)0x3U, s0) ^ (s1 ^ s2));
}

static void mixColumns0(uint8_t *state)
{
  mixColumns_0(state, (uint32_t)0U);
  mixColumns_0(state, (uint32_t)1U);
  mixColumns_0(state, (uint32_t)2U);
  mixColumns_0(state, (uint32_t)3U);
}

static void addRoundKey_0(uint8_t *state, uint8_t *w, uint32_t round, uint32_t c)
{
  uint8_t *target = state + (uint32_t)4U * c;
  uint8_t *subkey = w + (uint32_t)16U * round + (uint32_t)4U * c;
  target[0U] = target[0U] ^ subkey[0U];
  target[1U] = target[1U] ^ subkey[1U];
  target[2U] = target[2U] ^ subkey[2U];
  target[3U] = target[3U] ^ subkey[3U];
}

static void addRoundKey0(uint8_t *state, uint8_t *w, uint32_t round)
{
  addRoundKey_0(state, w, round, (uint32_t)0U);
  addRoundKey_0(state, w, round, (uint32_t)1U);
  addRoundKey_0(state, w, round, (uint32_t)2U);
  addRoundKey_0(state, w, round, (uint32_t)3U);
}

static void cipher_loop0(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t)10U)
  {
    subBytes_sbox0(state, sbox);
    shiftRows0(state);
    mixColumns0(state);
    addRoundKey0(state, w, round);
    cipher_loop0(state, w, sbox, round + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES128_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (input[0U]));
  addRoundKey0(state, w, (uint32_t)0U);
  cipher_loop0(state, w, sbox, (uint32_t)1U);
  subBytes_sbox0(state, sbox);
  shiftRows0(state);
  addRoundKey0(state, w, (uint32_t)10U);
  memcpy(out, state, (uint32_t)16U * sizeof (state[0U]));
}

static void rotWord0(uint8_t *word)
{
  uint8_t w0 = word[0U];
  uint8_t w1 = word[1U];
  uint8_t w2 = word[2U];
  uint8_t w3 = word[3U];
  word[0U] = w1;
  word[1U] = w2;
  word[2U] = w3;
  word[3U] = w0;
}

static void subWord0(uint8_t *word, uint8_t *sbox)
{
  word[0U] = access0(sbox, word[0U]);
  word[1U] = access0(sbox, word[1U]);
  word[2U] = access0(sbox, word[2U]);
  word[3U] = access0(sbox, word[3U]);
}

static uint8_t rcon0(uint32_t i, uint8_t tmp)
{
  if (i == (uint32_t)1U)
  {
    return tmp;
  }
  else
  {
    uint8_t tmp1 = multiply0((uint8_t)0x2U, tmp);
    return rcon0(i - (uint32_t)1U, tmp1);
  }
}

static void keyExpansion_aux_00(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  memcpy(temp, w + (uint32_t)4U * j - (uint32_t)4U, (uint32_t)4U * sizeof (w[0U]));
  if (j % (uint32_t)4U == (uint32_t)0U)
  {
    rotWord0(temp);
    subWord0(temp, sbox);
    uint8_t t0 = temp[0U];
    uint8_t rc = rcon0(j / (uint32_t)4U, (uint8_t)1U);
    uint8_t z = t0 ^ rc;
    temp[0U] = z;
  }
  else if (j % (uint32_t)4U == (uint32_t)4U)
  {
    subWord0(temp, sbox);
  }
}

static void keyExpansion_aux_10(uint8_t *w, uint8_t *temp, uint32_t j)
{
  uint32_t i = (uint32_t)4U * j;
  uint8_t w0 = w[i + (uint32_t)0U - (uint32_t)16U];
  uint8_t w1 = w[i + (uint32_t)1U - (uint32_t)16U];
  uint8_t w2 = w[i + (uint32_t)2U - (uint32_t)16U];
  uint8_t w3 = w[i + (uint32_t)3U - (uint32_t)16U];
  uint8_t t0 = temp[0U];
  uint8_t t1 = temp[1U];
  uint8_t t2 = temp[2U];
  uint8_t t3 = temp[3U];
  w[i + (uint32_t)0U] = t0 ^ w0;
  w[i + (uint32_t)1U] = t1 ^ w1;
  w[i + (uint32_t)2U] = t2 ^ w2;
  w[i + (uint32_t)3U] = t3 ^ w3;
}

static void keyExpansion_aux0(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  if (j < (uint32_t)44U)
  {
    keyExpansion_aux_00(w, temp, sbox, j);
    keyExpansion_aux_10(w, temp, j);
    keyExpansion_aux0(w, temp, sbox, j + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox)
{
  uint8_t temp[4U] = { 0U };
  memcpy(w, key, (uint32_t)16U * sizeof (key[0U]));
  keyExpansion_aux0(w, temp, sbox, (uint32_t)4U);
}

static void invSubBytes_aux_sbox0(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (!(ctr == (uint32_t)16U))
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access0(sbox, si);
    state[ctr] = si_;
    invSubBytes_aux_sbox0(state, sbox, ctr + (uint32_t)1U);
  }
}

static void invSubBytes_sbox0(uint8_t *state, uint8_t *sbox)
{
  invSubBytes_aux_sbox0(state, sbox, (uint32_t)0U);
}

static void invShiftRows0(uint8_t *state)
{
  uint32_t i = (uint32_t)3U;
  uint8_t tmp = state[i];
  state[i] = state[i + (uint32_t)4U];
  state[i + (uint32_t)4U] = state[i + (uint32_t)8U];
  state[i + (uint32_t)8U] = state[i + (uint32_t)12U];
  state[i + (uint32_t)12U] = tmp;
  uint32_t i1 = (uint32_t)2U;
  uint8_t tmp1 = state[i1];
  state[i1] = state[i1 + (uint32_t)8U];
  state[i1 + (uint32_t)8U] = tmp1;
  uint8_t tmp2 = state[i1 + (uint32_t)4U];
  state[i1 + (uint32_t)4U] = state[i1 + (uint32_t)12U];
  state[i1 + (uint32_t)12U] = tmp2;
  uint32_t i2 = (uint32_t)1U;
  uint8_t tmp3 = state[i2];
  state[i2] = state[i2 + (uint32_t)12U];
  state[i2 + (uint32_t)12U] = state[i2 + (uint32_t)8U];
  state[i2 + (uint32_t)8U] = state[i2 + (uint32_t)4U];
  state[i2 + (uint32_t)4U] = tmp3;
}

static void invMixColumns_0(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t)4U * c;
  uint8_t s0 = s[0U];
  uint8_t s1 = s[1U];
  uint8_t s2 = s[2U];
  uint8_t s3 = s[3U];
  s[0U] =
    multiply0((uint8_t)0xeU,
      s0)
    ^
      (multiply0((uint8_t)0xbU, s1) ^ (multiply0((uint8_t)0xdU, s2) ^ multiply0((uint8_t)0x9U, s3)));
  s[1U] =
    multiply0((uint8_t)0xeU,
      s1)
    ^
      (multiply0((uint8_t)0xbU, s2) ^ (multiply0((uint8_t)0xdU, s3) ^ multiply0((uint8_t)0x9U, s0)));
  s[2U] =
    multiply0((uint8_t)0xeU,
      s2)
    ^
      (multiply0((uint8_t)0xbU, s3) ^ (multiply0((uint8_t)0xdU, s0) ^ multiply0((uint8_t)0x9U, s1)));
  s[3U] =
    multiply0((uint8_t)0xeU,
      s3)
    ^
      (multiply0((uint8_t)0xbU, s0) ^ (multiply0((uint8_t)0xdU, s1) ^ multiply0((uint8_t)0x9U, s2)));
}

static void invMixColumns0(uint8_t *state)
{
  invMixColumns_0(state, (uint32_t)0U);
  invMixColumns_0(state, (uint32_t)1U);
  invMixColumns_0(state, (uint32_t)2U);
  invMixColumns_0(state, (uint32_t)3U);
}

static void inv_cipher_loop0(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t)0U)
  {
    invShiftRows0(state);
    invSubBytes_sbox0(state, sbox);
    addRoundKey0(state, w, round);
    invMixColumns0(state);
    inv_cipher_loop0(state, w, sbox, round - (uint32_t)1U);
  }
}

void
Crypto_Symmetric_AES128_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (input[0U]));
  addRoundKey0(state, w, (uint32_t)10U);
  inv_cipher_loop0(state, w, sbox, (uint32_t)9U);
  invShiftRows0(state);
  invSubBytes_sbox0(state, sbox);
  addRoundKey0(state, w, (uint32_t)0U);
  memcpy(out, state, (uint32_t)16U * sizeof (state[0U]));
}

