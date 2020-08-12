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

void Crypto_Symmetric_AES_mk_sbox(uint8_t *sbox1)
{
  sbox1[0U] = (uint8_t)0x63U;
  sbox1[1U] = (uint8_t)0x7cU;
  sbox1[2U] = (uint8_t)0x77U;
  sbox1[3U] = (uint8_t)0x7bU;
  sbox1[4U] = (uint8_t)0xf2U;
  sbox1[5U] = (uint8_t)0x6bU;
  sbox1[6U] = (uint8_t)0x6fU;
  sbox1[7U] = (uint8_t)0xc5U;
  sbox1[8U] = (uint8_t)0x30U;
  sbox1[9U] = (uint8_t)0x01U;
  sbox1[10U] = (uint8_t)0x67U;
  sbox1[11U] = (uint8_t)0x2bU;
  sbox1[12U] = (uint8_t)0xfeU;
  sbox1[13U] = (uint8_t)0xd7U;
  sbox1[14U] = (uint8_t)0xabU;
  sbox1[15U] = (uint8_t)0x76U;
  sbox1[16U] = (uint8_t)0xcaU;
  sbox1[17U] = (uint8_t)0x82U;
  sbox1[18U] = (uint8_t)0xc9U;
  sbox1[19U] = (uint8_t)0x7dU;
  sbox1[20U] = (uint8_t)0xfaU;
  sbox1[21U] = (uint8_t)0x59U;
  sbox1[22U] = (uint8_t)0x47U;
  sbox1[23U] = (uint8_t)0xf0U;
  sbox1[24U] = (uint8_t)0xadU;
  sbox1[25U] = (uint8_t)0xd4U;
  sbox1[26U] = (uint8_t)0xa2U;
  sbox1[27U] = (uint8_t)0xafU;
  sbox1[28U] = (uint8_t)0x9cU;
  sbox1[29U] = (uint8_t)0xa4U;
  sbox1[30U] = (uint8_t)0x72U;
  sbox1[31U] = (uint8_t)0xc0U;
  sbox1[32U] = (uint8_t)0xb7U;
  sbox1[33U] = (uint8_t)0xfdU;
  sbox1[34U] = (uint8_t)0x93U;
  sbox1[35U] = (uint8_t)0x26U;
  sbox1[36U] = (uint8_t)0x36U;
  sbox1[37U] = (uint8_t)0x3fU;
  sbox1[38U] = (uint8_t)0xf7U;
  sbox1[39U] = (uint8_t)0xccU;
  sbox1[40U] = (uint8_t)0x34U;
  sbox1[41U] = (uint8_t)0xa5U;
  sbox1[42U] = (uint8_t)0xe5U;
  sbox1[43U] = (uint8_t)0xf1U;
  sbox1[44U] = (uint8_t)0x71U;
  sbox1[45U] = (uint8_t)0xd8U;
  sbox1[46U] = (uint8_t)0x31U;
  sbox1[47U] = (uint8_t)0x15U;
  sbox1[48U] = (uint8_t)0x04U;
  sbox1[49U] = (uint8_t)0xc7U;
  sbox1[50U] = (uint8_t)0x23U;
  sbox1[51U] = (uint8_t)0xc3U;
  sbox1[52U] = (uint8_t)0x18U;
  sbox1[53U] = (uint8_t)0x96U;
  sbox1[54U] = (uint8_t)0x05U;
  sbox1[55U] = (uint8_t)0x9aU;
  sbox1[56U] = (uint8_t)0x07U;
  sbox1[57U] = (uint8_t)0x12U;
  sbox1[58U] = (uint8_t)0x80U;
  sbox1[59U] = (uint8_t)0xe2U;
  sbox1[60U] = (uint8_t)0xebU;
  sbox1[61U] = (uint8_t)0x27U;
  sbox1[62U] = (uint8_t)0xb2U;
  sbox1[63U] = (uint8_t)0x75U;
  sbox1[64U] = (uint8_t)0x09U;
  sbox1[65U] = (uint8_t)0x83U;
  sbox1[66U] = (uint8_t)0x2cU;
  sbox1[67U] = (uint8_t)0x1aU;
  sbox1[68U] = (uint8_t)0x1bU;
  sbox1[69U] = (uint8_t)0x6eU;
  sbox1[70U] = (uint8_t)0x5aU;
  sbox1[71U] = (uint8_t)0xa0U;
  sbox1[72U] = (uint8_t)0x52U;
  sbox1[73U] = (uint8_t)0x3bU;
  sbox1[74U] = (uint8_t)0xd6U;
  sbox1[75U] = (uint8_t)0xb3U;
  sbox1[76U] = (uint8_t)0x29U;
  sbox1[77U] = (uint8_t)0xe3U;
  sbox1[78U] = (uint8_t)0x2fU;
  sbox1[79U] = (uint8_t)0x84U;
  sbox1[80U] = (uint8_t)0x53U;
  sbox1[81U] = (uint8_t)0xd1U;
  sbox1[82U] = (uint8_t)0x00U;
  sbox1[83U] = (uint8_t)0xedU;
  sbox1[84U] = (uint8_t)0x20U;
  sbox1[85U] = (uint8_t)0xfcU;
  sbox1[86U] = (uint8_t)0xb1U;
  sbox1[87U] = (uint8_t)0x5bU;
  sbox1[88U] = (uint8_t)0x6aU;
  sbox1[89U] = (uint8_t)0xcbU;
  sbox1[90U] = (uint8_t)0xbeU;
  sbox1[91U] = (uint8_t)0x39U;
  sbox1[92U] = (uint8_t)0x4aU;
  sbox1[93U] = (uint8_t)0x4cU;
  sbox1[94U] = (uint8_t)0x58U;
  sbox1[95U] = (uint8_t)0xcfU;
  sbox1[96U] = (uint8_t)0xd0U;
  sbox1[97U] = (uint8_t)0xefU;
  sbox1[98U] = (uint8_t)0xaaU;
  sbox1[99U] = (uint8_t)0xfbU;
  sbox1[100U] = (uint8_t)0x43U;
  sbox1[101U] = (uint8_t)0x4dU;
  sbox1[102U] = (uint8_t)0x33U;
  sbox1[103U] = (uint8_t)0x85U;
  sbox1[104U] = (uint8_t)0x45U;
  sbox1[105U] = (uint8_t)0xf9U;
  sbox1[106U] = (uint8_t)0x02U;
  sbox1[107U] = (uint8_t)0x7fU;
  sbox1[108U] = (uint8_t)0x50U;
  sbox1[109U] = (uint8_t)0x3cU;
  sbox1[110U] = (uint8_t)0x9fU;
  sbox1[111U] = (uint8_t)0xa8U;
  sbox1[112U] = (uint8_t)0x51U;
  sbox1[113U] = (uint8_t)0xa3U;
  sbox1[114U] = (uint8_t)0x40U;
  sbox1[115U] = (uint8_t)0x8fU;
  sbox1[116U] = (uint8_t)0x92U;
  sbox1[117U] = (uint8_t)0x9dU;
  sbox1[118U] = (uint8_t)0x38U;
  sbox1[119U] = (uint8_t)0xf5U;
  sbox1[120U] = (uint8_t)0xbcU;
  sbox1[121U] = (uint8_t)0xb6U;
  sbox1[122U] = (uint8_t)0xdaU;
  sbox1[123U] = (uint8_t)0x21U;
  sbox1[124U] = (uint8_t)0x10U;
  sbox1[125U] = (uint8_t)0xffU;
  sbox1[126U] = (uint8_t)0xf3U;
  sbox1[127U] = (uint8_t)0xd2U;
  sbox1[128U] = (uint8_t)0xcdU;
  sbox1[129U] = (uint8_t)0x0cU;
  sbox1[130U] = (uint8_t)0x13U;
  sbox1[131U] = (uint8_t)0xecU;
  sbox1[132U] = (uint8_t)0x5fU;
  sbox1[133U] = (uint8_t)0x97U;
  sbox1[134U] = (uint8_t)0x44U;
  sbox1[135U] = (uint8_t)0x17U;
  sbox1[136U] = (uint8_t)0xc4U;
  sbox1[137U] = (uint8_t)0xa7U;
  sbox1[138U] = (uint8_t)0x7eU;
  sbox1[139U] = (uint8_t)0x3dU;
  sbox1[140U] = (uint8_t)0x64U;
  sbox1[141U] = (uint8_t)0x5dU;
  sbox1[142U] = (uint8_t)0x19U;
  sbox1[143U] = (uint8_t)0x73U;
  sbox1[144U] = (uint8_t)0x60U;
  sbox1[145U] = (uint8_t)0x81U;
  sbox1[146U] = (uint8_t)0x4fU;
  sbox1[147U] = (uint8_t)0xdcU;
  sbox1[148U] = (uint8_t)0x22U;
  sbox1[149U] = (uint8_t)0x2aU;
  sbox1[150U] = (uint8_t)0x90U;
  sbox1[151U] = (uint8_t)0x88U;
  sbox1[152U] = (uint8_t)0x46U;
  sbox1[153U] = (uint8_t)0xeeU;
  sbox1[154U] = (uint8_t)0xb8U;
  sbox1[155U] = (uint8_t)0x14U;
  sbox1[156U] = (uint8_t)0xdeU;
  sbox1[157U] = (uint8_t)0x5eU;
  sbox1[158U] = (uint8_t)0x0bU;
  sbox1[159U] = (uint8_t)0xdbU;
  sbox1[160U] = (uint8_t)0xe0U;
  sbox1[161U] = (uint8_t)0x32U;
  sbox1[162U] = (uint8_t)0x3aU;
  sbox1[163U] = (uint8_t)0x0aU;
  sbox1[164U] = (uint8_t)0x49U;
  sbox1[165U] = (uint8_t)0x06U;
  sbox1[166U] = (uint8_t)0x24U;
  sbox1[167U] = (uint8_t)0x5cU;
  sbox1[168U] = (uint8_t)0xc2U;
  sbox1[169U] = (uint8_t)0xd3U;
  sbox1[170U] = (uint8_t)0xacU;
  sbox1[171U] = (uint8_t)0x62U;
  sbox1[172U] = (uint8_t)0x91U;
  sbox1[173U] = (uint8_t)0x95U;
  sbox1[174U] = (uint8_t)0xe4U;
  sbox1[175U] = (uint8_t)0x79U;
  sbox1[176U] = (uint8_t)0xe7U;
  sbox1[177U] = (uint8_t)0xc8U;
  sbox1[178U] = (uint8_t)0x37U;
  sbox1[179U] = (uint8_t)0x6dU;
  sbox1[180U] = (uint8_t)0x8dU;
  sbox1[181U] = (uint8_t)0xd5U;
  sbox1[182U] = (uint8_t)0x4eU;
  sbox1[183U] = (uint8_t)0xa9U;
  sbox1[184U] = (uint8_t)0x6cU;
  sbox1[185U] = (uint8_t)0x56U;
  sbox1[186U] = (uint8_t)0xf4U;
  sbox1[187U] = (uint8_t)0xeaU;
  sbox1[188U] = (uint8_t)0x65U;
  sbox1[189U] = (uint8_t)0x7aU;
  sbox1[190U] = (uint8_t)0xaeU;
  sbox1[191U] = (uint8_t)0x08U;
  sbox1[192U] = (uint8_t)0xbaU;
  sbox1[193U] = (uint8_t)0x78U;
  sbox1[194U] = (uint8_t)0x25U;
  sbox1[195U] = (uint8_t)0x2eU;
  sbox1[196U] = (uint8_t)0x1cU;
  sbox1[197U] = (uint8_t)0xa6U;
  sbox1[198U] = (uint8_t)0xb4U;
  sbox1[199U] = (uint8_t)0xc6U;
  sbox1[200U] = (uint8_t)0xe8U;
  sbox1[201U] = (uint8_t)0xddU;
  sbox1[202U] = (uint8_t)0x74U;
  sbox1[203U] = (uint8_t)0x1fU;
  sbox1[204U] = (uint8_t)0x4bU;
  sbox1[205U] = (uint8_t)0xbdU;
  sbox1[206U] = (uint8_t)0x8bU;
  sbox1[207U] = (uint8_t)0x8aU;
  sbox1[208U] = (uint8_t)0x70U;
  sbox1[209U] = (uint8_t)0x3eU;
  sbox1[210U] = (uint8_t)0xb5U;
  sbox1[211U] = (uint8_t)0x66U;
  sbox1[212U] = (uint8_t)0x48U;
  sbox1[213U] = (uint8_t)0x03U;
  sbox1[214U] = (uint8_t)0xf6U;
  sbox1[215U] = (uint8_t)0x0eU;
  sbox1[216U] = (uint8_t)0x61U;
  sbox1[217U] = (uint8_t)0x35U;
  sbox1[218U] = (uint8_t)0x57U;
  sbox1[219U] = (uint8_t)0xb9U;
  sbox1[220U] = (uint8_t)0x86U;
  sbox1[221U] = (uint8_t)0xc1U;
  sbox1[222U] = (uint8_t)0x1dU;
  sbox1[223U] = (uint8_t)0x9eU;
  sbox1[224U] = (uint8_t)0xe1U;
  sbox1[225U] = (uint8_t)0xf8U;
  sbox1[226U] = (uint8_t)0x98U;
  sbox1[227U] = (uint8_t)0x11U;
  sbox1[228U] = (uint8_t)0x69U;
  sbox1[229U] = (uint8_t)0xd9U;
  sbox1[230U] = (uint8_t)0x8eU;
  sbox1[231U] = (uint8_t)0x94U;
  sbox1[232U] = (uint8_t)0x9bU;
  sbox1[233U] = (uint8_t)0x1eU;
  sbox1[234U] = (uint8_t)0x87U;
  sbox1[235U] = (uint8_t)0xe9U;
  sbox1[236U] = (uint8_t)0xceU;
  sbox1[237U] = (uint8_t)0x55U;
  sbox1[238U] = (uint8_t)0x28U;
  sbox1[239U] = (uint8_t)0xdfU;
  sbox1[240U] = (uint8_t)0x8cU;
  sbox1[241U] = (uint8_t)0xa1U;
  sbox1[242U] = (uint8_t)0x89U;
  sbox1[243U] = (uint8_t)0x0dU;
  sbox1[244U] = (uint8_t)0xbfU;
  sbox1[245U] = (uint8_t)0xe6U;
  sbox1[246U] = (uint8_t)0x42U;
  sbox1[247U] = (uint8_t)0x68U;
  sbox1[248U] = (uint8_t)0x41U;
  sbox1[249U] = (uint8_t)0x99U;
  sbox1[250U] = (uint8_t)0x2dU;
  sbox1[251U] = (uint8_t)0x0fU;
  sbox1[252U] = (uint8_t)0xb0U;
  sbox1[253U] = (uint8_t)0x54U;
  sbox1[254U] = (uint8_t)0xbbU;
  sbox1[255U] = (uint8_t)0x16U;
}

void Crypto_Symmetric_AES_mk_inv_sbox(uint8_t *sbox1)
{
  sbox1[0U] = (uint8_t)0x52U;
  sbox1[1U] = (uint8_t)0x09U;
  sbox1[2U] = (uint8_t)0x6aU;
  sbox1[3U] = (uint8_t)0xd5U;
  sbox1[4U] = (uint8_t)0x30U;
  sbox1[5U] = (uint8_t)0x36U;
  sbox1[6U] = (uint8_t)0xa5U;
  sbox1[7U] = (uint8_t)0x38U;
  sbox1[8U] = (uint8_t)0xbfU;
  sbox1[9U] = (uint8_t)0x40U;
  sbox1[10U] = (uint8_t)0xa3U;
  sbox1[11U] = (uint8_t)0x9eU;
  sbox1[12U] = (uint8_t)0x81U;
  sbox1[13U] = (uint8_t)0xf3U;
  sbox1[14U] = (uint8_t)0xd7U;
  sbox1[15U] = (uint8_t)0xfbU;
  sbox1[16U] = (uint8_t)0x7cU;
  sbox1[17U] = (uint8_t)0xe3U;
  sbox1[18U] = (uint8_t)0x39U;
  sbox1[19U] = (uint8_t)0x82U;
  sbox1[20U] = (uint8_t)0x9bU;
  sbox1[21U] = (uint8_t)0x2fU;
  sbox1[22U] = (uint8_t)0xffU;
  sbox1[23U] = (uint8_t)0x87U;
  sbox1[24U] = (uint8_t)0x34U;
  sbox1[25U] = (uint8_t)0x8eU;
  sbox1[26U] = (uint8_t)0x43U;
  sbox1[27U] = (uint8_t)0x44U;
  sbox1[28U] = (uint8_t)0xc4U;
  sbox1[29U] = (uint8_t)0xdeU;
  sbox1[30U] = (uint8_t)0xe9U;
  sbox1[31U] = (uint8_t)0xcbU;
  sbox1[32U] = (uint8_t)0x54U;
  sbox1[33U] = (uint8_t)0x7bU;
  sbox1[34U] = (uint8_t)0x94U;
  sbox1[35U] = (uint8_t)0x32U;
  sbox1[36U] = (uint8_t)0xa6U;
  sbox1[37U] = (uint8_t)0xc2U;
  sbox1[38U] = (uint8_t)0x23U;
  sbox1[39U] = (uint8_t)0x3dU;
  sbox1[40U] = (uint8_t)0xeeU;
  sbox1[41U] = (uint8_t)0x4cU;
  sbox1[42U] = (uint8_t)0x95U;
  sbox1[43U] = (uint8_t)0x0bU;
  sbox1[44U] = (uint8_t)0x42U;
  sbox1[45U] = (uint8_t)0xfaU;
  sbox1[46U] = (uint8_t)0xc3U;
  sbox1[47U] = (uint8_t)0x4eU;
  sbox1[48U] = (uint8_t)0x08U;
  sbox1[49U] = (uint8_t)0x2eU;
  sbox1[50U] = (uint8_t)0xa1U;
  sbox1[51U] = (uint8_t)0x66U;
  sbox1[52U] = (uint8_t)0x28U;
  sbox1[53U] = (uint8_t)0xd9U;
  sbox1[54U] = (uint8_t)0x24U;
  sbox1[55U] = (uint8_t)0xb2U;
  sbox1[56U] = (uint8_t)0x76U;
  sbox1[57U] = (uint8_t)0x5bU;
  sbox1[58U] = (uint8_t)0xa2U;
  sbox1[59U] = (uint8_t)0x49U;
  sbox1[60U] = (uint8_t)0x6dU;
  sbox1[61U] = (uint8_t)0x8bU;
  sbox1[62U] = (uint8_t)0xd1U;
  sbox1[63U] = (uint8_t)0x25U;
  sbox1[64U] = (uint8_t)0x72U;
  sbox1[65U] = (uint8_t)0xf8U;
  sbox1[66U] = (uint8_t)0xf6U;
  sbox1[67U] = (uint8_t)0x64U;
  sbox1[68U] = (uint8_t)0x86U;
  sbox1[69U] = (uint8_t)0x68U;
  sbox1[70U] = (uint8_t)0x98U;
  sbox1[71U] = (uint8_t)0x16U;
  sbox1[72U] = (uint8_t)0xd4U;
  sbox1[73U] = (uint8_t)0xa4U;
  sbox1[74U] = (uint8_t)0x5cU;
  sbox1[75U] = (uint8_t)0xccU;
  sbox1[76U] = (uint8_t)0x5dU;
  sbox1[77U] = (uint8_t)0x65U;
  sbox1[78U] = (uint8_t)0xb6U;
  sbox1[79U] = (uint8_t)0x92U;
  sbox1[80U] = (uint8_t)0x6cU;
  sbox1[81U] = (uint8_t)0x70U;
  sbox1[82U] = (uint8_t)0x48U;
  sbox1[83U] = (uint8_t)0x50U;
  sbox1[84U] = (uint8_t)0xfdU;
  sbox1[85U] = (uint8_t)0xedU;
  sbox1[86U] = (uint8_t)0xb9U;
  sbox1[87U] = (uint8_t)0xdaU;
  sbox1[88U] = (uint8_t)0x5eU;
  sbox1[89U] = (uint8_t)0x15U;
  sbox1[90U] = (uint8_t)0x46U;
  sbox1[91U] = (uint8_t)0x57U;
  sbox1[92U] = (uint8_t)0xa7U;
  sbox1[93U] = (uint8_t)0x8dU;
  sbox1[94U] = (uint8_t)0x9dU;
  sbox1[95U] = (uint8_t)0x84U;
  sbox1[96U] = (uint8_t)0x90U;
  sbox1[97U] = (uint8_t)0xd8U;
  sbox1[98U] = (uint8_t)0xabU;
  sbox1[99U] = (uint8_t)0x00U;
  sbox1[100U] = (uint8_t)0x8cU;
  sbox1[101U] = (uint8_t)0xbcU;
  sbox1[102U] = (uint8_t)0xd3U;
  sbox1[103U] = (uint8_t)0x0aU;
  sbox1[104U] = (uint8_t)0xf7U;
  sbox1[105U] = (uint8_t)0xe4U;
  sbox1[106U] = (uint8_t)0x58U;
  sbox1[107U] = (uint8_t)0x05U;
  sbox1[108U] = (uint8_t)0xb8U;
  sbox1[109U] = (uint8_t)0xb3U;
  sbox1[110U] = (uint8_t)0x45U;
  sbox1[111U] = (uint8_t)0x06U;
  sbox1[112U] = (uint8_t)0xd0U;
  sbox1[113U] = (uint8_t)0x2cU;
  sbox1[114U] = (uint8_t)0x1eU;
  sbox1[115U] = (uint8_t)0x8fU;
  sbox1[116U] = (uint8_t)0xcaU;
  sbox1[117U] = (uint8_t)0x3fU;
  sbox1[118U] = (uint8_t)0x0fU;
  sbox1[119U] = (uint8_t)0x02U;
  sbox1[120U] = (uint8_t)0xc1U;
  sbox1[121U] = (uint8_t)0xafU;
  sbox1[122U] = (uint8_t)0xbdU;
  sbox1[123U] = (uint8_t)0x03U;
  sbox1[124U] = (uint8_t)0x01U;
  sbox1[125U] = (uint8_t)0x13U;
  sbox1[126U] = (uint8_t)0x8aU;
  sbox1[127U] = (uint8_t)0x6bU;
  sbox1[128U] = (uint8_t)0x3aU;
  sbox1[129U] = (uint8_t)0x91U;
  sbox1[130U] = (uint8_t)0x11U;
  sbox1[131U] = (uint8_t)0x41U;
  sbox1[132U] = (uint8_t)0x4fU;
  sbox1[133U] = (uint8_t)0x67U;
  sbox1[134U] = (uint8_t)0xdcU;
  sbox1[135U] = (uint8_t)0xeaU;
  sbox1[136U] = (uint8_t)0x97U;
  sbox1[137U] = (uint8_t)0xf2U;
  sbox1[138U] = (uint8_t)0xcfU;
  sbox1[139U] = (uint8_t)0xceU;
  sbox1[140U] = (uint8_t)0xf0U;
  sbox1[141U] = (uint8_t)0xb4U;
  sbox1[142U] = (uint8_t)0xe6U;
  sbox1[143U] = (uint8_t)0x73U;
  sbox1[144U] = (uint8_t)0x96U;
  sbox1[145U] = (uint8_t)0xacU;
  sbox1[146U] = (uint8_t)0x74U;
  sbox1[147U] = (uint8_t)0x22U;
  sbox1[148U] = (uint8_t)0xe7U;
  sbox1[149U] = (uint8_t)0xadU;
  sbox1[150U] = (uint8_t)0x35U;
  sbox1[151U] = (uint8_t)0x85U;
  sbox1[152U] = (uint8_t)0xe2U;
  sbox1[153U] = (uint8_t)0xf9U;
  sbox1[154U] = (uint8_t)0x37U;
  sbox1[155U] = (uint8_t)0xe8U;
  sbox1[156U] = (uint8_t)0x1cU;
  sbox1[157U] = (uint8_t)0x75U;
  sbox1[158U] = (uint8_t)0xdfU;
  sbox1[159U] = (uint8_t)0x6eU;
  sbox1[160U] = (uint8_t)0x47U;
  sbox1[161U] = (uint8_t)0xf1U;
  sbox1[162U] = (uint8_t)0x1aU;
  sbox1[163U] = (uint8_t)0x71U;
  sbox1[164U] = (uint8_t)0x1dU;
  sbox1[165U] = (uint8_t)0x29U;
  sbox1[166U] = (uint8_t)0xc5U;
  sbox1[167U] = (uint8_t)0x89U;
  sbox1[168U] = (uint8_t)0x6fU;
  sbox1[169U] = (uint8_t)0xb7U;
  sbox1[170U] = (uint8_t)0x62U;
  sbox1[171U] = (uint8_t)0x0eU;
  sbox1[172U] = (uint8_t)0xaaU;
  sbox1[173U] = (uint8_t)0x18U;
  sbox1[174U] = (uint8_t)0xbeU;
  sbox1[175U] = (uint8_t)0x1bU;
  sbox1[176U] = (uint8_t)0xfcU;
  sbox1[177U] = (uint8_t)0x56U;
  sbox1[178U] = (uint8_t)0x3eU;
  sbox1[179U] = (uint8_t)0x4bU;
  sbox1[180U] = (uint8_t)0xc6U;
  sbox1[181U] = (uint8_t)0xd2U;
  sbox1[182U] = (uint8_t)0x79U;
  sbox1[183U] = (uint8_t)0x20U;
  sbox1[184U] = (uint8_t)0x9aU;
  sbox1[185U] = (uint8_t)0xdbU;
  sbox1[186U] = (uint8_t)0xc0U;
  sbox1[187U] = (uint8_t)0xfeU;
  sbox1[188U] = (uint8_t)0x78U;
  sbox1[189U] = (uint8_t)0xcdU;
  sbox1[190U] = (uint8_t)0x5aU;
  sbox1[191U] = (uint8_t)0xf4U;
  sbox1[192U] = (uint8_t)0x1fU;
  sbox1[193U] = (uint8_t)0xddU;
  sbox1[194U] = (uint8_t)0xa8U;
  sbox1[195U] = (uint8_t)0x33U;
  sbox1[196U] = (uint8_t)0x88U;
  sbox1[197U] = (uint8_t)0x07U;
  sbox1[198U] = (uint8_t)0xc7U;
  sbox1[199U] = (uint8_t)0x31U;
  sbox1[200U] = (uint8_t)0xb1U;
  sbox1[201U] = (uint8_t)0x12U;
  sbox1[202U] = (uint8_t)0x10U;
  sbox1[203U] = (uint8_t)0x59U;
  sbox1[204U] = (uint8_t)0x27U;
  sbox1[205U] = (uint8_t)0x80U;
  sbox1[206U] = (uint8_t)0xecU;
  sbox1[207U] = (uint8_t)0x5fU;
  sbox1[208U] = (uint8_t)0x60U;
  sbox1[209U] = (uint8_t)0x51U;
  sbox1[210U] = (uint8_t)0x7fU;
  sbox1[211U] = (uint8_t)0xa9U;
  sbox1[212U] = (uint8_t)0x19U;
  sbox1[213U] = (uint8_t)0xb5U;
  sbox1[214U] = (uint8_t)0x4aU;
  sbox1[215U] = (uint8_t)0x0dU;
  sbox1[216U] = (uint8_t)0x2dU;
  sbox1[217U] = (uint8_t)0xe5U;
  sbox1[218U] = (uint8_t)0x7aU;
  sbox1[219U] = (uint8_t)0x9fU;
  sbox1[220U] = (uint8_t)0x93U;
  sbox1[221U] = (uint8_t)0xc9U;
  sbox1[222U] = (uint8_t)0x9cU;
  sbox1[223U] = (uint8_t)0xefU;
  sbox1[224U] = (uint8_t)0xa0U;
  sbox1[225U] = (uint8_t)0xe0U;
  sbox1[226U] = (uint8_t)0x3bU;
  sbox1[227U] = (uint8_t)0x4dU;
  sbox1[228U] = (uint8_t)0xaeU;
  sbox1[229U] = (uint8_t)0x2aU;
  sbox1[230U] = (uint8_t)0xf5U;
  sbox1[231U] = (uint8_t)0xb0U;
  sbox1[232U] = (uint8_t)0xc8U;
  sbox1[233U] = (uint8_t)0xebU;
  sbox1[234U] = (uint8_t)0xbbU;
  sbox1[235U] = (uint8_t)0x3cU;
  sbox1[236U] = (uint8_t)0x83U;
  sbox1[237U] = (uint8_t)0x53U;
  sbox1[238U] = (uint8_t)0x99U;
  sbox1[239U] = (uint8_t)0x61U;
  sbox1[240U] = (uint8_t)0x17U;
  sbox1[241U] = (uint8_t)0x2bU;
  sbox1[242U] = (uint8_t)0x04U;
  sbox1[243U] = (uint8_t)0x7eU;
  sbox1[244U] = (uint8_t)0xbaU;
  sbox1[245U] = (uint8_t)0x77U;
  sbox1[246U] = (uint8_t)0xd6U;
  sbox1[247U] = (uint8_t)0x26U;
  sbox1[248U] = (uint8_t)0xe1U;
  sbox1[249U] = (uint8_t)0x69U;
  sbox1[250U] = (uint8_t)0x14U;
  sbox1[251U] = (uint8_t)0x63U;
  sbox1[252U] = (uint8_t)0x55U;
  sbox1[253U] = (uint8_t)0x21U;
  sbox1[254U] = (uint8_t)0x0cU;
  sbox1[255U] = (uint8_t)0x7dU;
}

#ifdef _MSC_VER
// Work around a /Ox code-gen bug in AES key expansion, in the MSVC compiler
#pragma optimize("", off)
#pragma optimize("s", on)
#endif

static uint8_t access(uint8_t *sbox1, uint8_t i)
{
  return sbox1[(uint32_t)i];
}

#ifdef _MSC_VER
#pragma optimize("", on)
#endif

static void subBytes_aux_sbox(uint8_t *state, uint8_t *sbox1, uint32_t ctr)
{
  if (ctr != (uint32_t)16U)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access(sbox1, si);
    state[ctr] = si_;
    subBytes_aux_sbox(state, sbox1, ctr + (uint32_t)1U);
  }
}

static void subBytes_sbox(uint8_t *state, uint8_t *sbox1)
{
  subBytes_aux_sbox(state, sbox1, (uint32_t)0U);
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

static void cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox1, uint32_t round)
{
  if (round != (uint32_t)14U)
  {
    subBytes_sbox(state, sbox1);
    shiftRows(state);
    mixColumns(state);
    addRoundKey(state, w, round);
    cipher_loop(state, w, sbox1, round + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (uint8_t));
  addRoundKey(state, w, (uint32_t)0U);
  cipher_loop(state, w, sbox1, (uint32_t)1U);
  subBytes_sbox(state, sbox1);
  shiftRows(state);
  addRoundKey(state, w, (uint32_t)14U);
  memcpy(out, state, (uint32_t)16U * sizeof (uint8_t));
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

static void subWord(uint8_t *word, uint8_t *sbox1)
{
  word[0U] = access(sbox1, word[0U]);
  word[1U] = access(sbox1, word[1U]);
  word[2U] = access(sbox1, word[2U]);
  word[3U] = access(sbox1, word[3U]);
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

static void keyExpansion_aux_0(uint8_t *w, uint8_t *temp, uint8_t *sbox1, uint32_t j)
{
  memcpy(temp, w + (uint32_t)4U * j - (uint32_t)4U, (uint32_t)4U * sizeof (uint8_t));
  if (j % (uint32_t)8U == (uint32_t)0U)
  {
    rotWord(temp);
    subWord(temp, sbox1);
    uint8_t t0 = temp[0U];
    uint8_t rc = rcon(j / (uint32_t)8U, (uint8_t)1U);
    uint8_t z = t0 ^ rc;
    temp[0U] = z;
  }
  else if (j % (uint32_t)8U == (uint32_t)4U)
  {
    subWord(temp, sbox1);
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

static void keyExpansion_aux(uint8_t *w, uint8_t *temp, uint8_t *sbox1, uint32_t j)
{
  if (j < (uint32_t)60U)
  {
    keyExpansion_aux_0(w, temp, sbox1, j);
    keyExpansion_aux_1(w, temp, j);
    keyExpansion_aux(w, temp, sbox1, j + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox1)
{
  uint8_t temp[4U] = { 0U };
  memcpy(w, key, (uint32_t)32U * sizeof (uint8_t));
  keyExpansion_aux(w, temp, sbox1, (uint32_t)8U);
}

static void invSubBytes_aux_sbox(uint8_t *state, uint8_t *sbox1, uint32_t ctr)
{
  if (!(ctr == (uint32_t)16U))
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access(sbox1, si);
    state[ctr] = si_;
    invSubBytes_aux_sbox(state, sbox1, ctr + (uint32_t)1U);
  }
}

static void invSubBytes_sbox(uint8_t *state, uint8_t *sbox1)
{
  invSubBytes_aux_sbox(state, sbox1, (uint32_t)0U);
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

static void inv_cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox1, uint32_t round)
{
  if (round != (uint32_t)0U)
  {
    invShiftRows(state);
    invSubBytes_sbox(state, sbox1);
    addRoundKey(state, w, round);
    invMixColumns(state);
    inv_cipher_loop(state, w, sbox1, round - (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (uint8_t));
  addRoundKey(state, w, (uint32_t)14U);
  inv_cipher_loop(state, w, sbox1, (uint32_t)13U);
  invShiftRows(state);
  invSubBytes_sbox(state, sbox1);
  addRoundKey(state, w, (uint32_t)0U);
  memcpy(out, state, (uint32_t)16U * sizeof (uint8_t));
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

void Crypto_Symmetric_AES128_mk_sbox(uint8_t *sbox1)
{
  sbox1[0U] = (uint8_t)0x63U;
  sbox1[1U] = (uint8_t)0x7cU;
  sbox1[2U] = (uint8_t)0x77U;
  sbox1[3U] = (uint8_t)0x7bU;
  sbox1[4U] = (uint8_t)0xf2U;
  sbox1[5U] = (uint8_t)0x6bU;
  sbox1[6U] = (uint8_t)0x6fU;
  sbox1[7U] = (uint8_t)0xc5U;
  sbox1[8U] = (uint8_t)0x30U;
  sbox1[9U] = (uint8_t)0x01U;
  sbox1[10U] = (uint8_t)0x67U;
  sbox1[11U] = (uint8_t)0x2bU;
  sbox1[12U] = (uint8_t)0xfeU;
  sbox1[13U] = (uint8_t)0xd7U;
  sbox1[14U] = (uint8_t)0xabU;
  sbox1[15U] = (uint8_t)0x76U;
  sbox1[16U] = (uint8_t)0xcaU;
  sbox1[17U] = (uint8_t)0x82U;
  sbox1[18U] = (uint8_t)0xc9U;
  sbox1[19U] = (uint8_t)0x7dU;
  sbox1[20U] = (uint8_t)0xfaU;
  sbox1[21U] = (uint8_t)0x59U;
  sbox1[22U] = (uint8_t)0x47U;
  sbox1[23U] = (uint8_t)0xf0U;
  sbox1[24U] = (uint8_t)0xadU;
  sbox1[25U] = (uint8_t)0xd4U;
  sbox1[26U] = (uint8_t)0xa2U;
  sbox1[27U] = (uint8_t)0xafU;
  sbox1[28U] = (uint8_t)0x9cU;
  sbox1[29U] = (uint8_t)0xa4U;
  sbox1[30U] = (uint8_t)0x72U;
  sbox1[31U] = (uint8_t)0xc0U;
  sbox1[32U] = (uint8_t)0xb7U;
  sbox1[33U] = (uint8_t)0xfdU;
  sbox1[34U] = (uint8_t)0x93U;
  sbox1[35U] = (uint8_t)0x26U;
  sbox1[36U] = (uint8_t)0x36U;
  sbox1[37U] = (uint8_t)0x3fU;
  sbox1[38U] = (uint8_t)0xf7U;
  sbox1[39U] = (uint8_t)0xccU;
  sbox1[40U] = (uint8_t)0x34U;
  sbox1[41U] = (uint8_t)0xa5U;
  sbox1[42U] = (uint8_t)0xe5U;
  sbox1[43U] = (uint8_t)0xf1U;
  sbox1[44U] = (uint8_t)0x71U;
  sbox1[45U] = (uint8_t)0xd8U;
  sbox1[46U] = (uint8_t)0x31U;
  sbox1[47U] = (uint8_t)0x15U;
  sbox1[48U] = (uint8_t)0x04U;
  sbox1[49U] = (uint8_t)0xc7U;
  sbox1[50U] = (uint8_t)0x23U;
  sbox1[51U] = (uint8_t)0xc3U;
  sbox1[52U] = (uint8_t)0x18U;
  sbox1[53U] = (uint8_t)0x96U;
  sbox1[54U] = (uint8_t)0x05U;
  sbox1[55U] = (uint8_t)0x9aU;
  sbox1[56U] = (uint8_t)0x07U;
  sbox1[57U] = (uint8_t)0x12U;
  sbox1[58U] = (uint8_t)0x80U;
  sbox1[59U] = (uint8_t)0xe2U;
  sbox1[60U] = (uint8_t)0xebU;
  sbox1[61U] = (uint8_t)0x27U;
  sbox1[62U] = (uint8_t)0xb2U;
  sbox1[63U] = (uint8_t)0x75U;
  sbox1[64U] = (uint8_t)0x09U;
  sbox1[65U] = (uint8_t)0x83U;
  sbox1[66U] = (uint8_t)0x2cU;
  sbox1[67U] = (uint8_t)0x1aU;
  sbox1[68U] = (uint8_t)0x1bU;
  sbox1[69U] = (uint8_t)0x6eU;
  sbox1[70U] = (uint8_t)0x5aU;
  sbox1[71U] = (uint8_t)0xa0U;
  sbox1[72U] = (uint8_t)0x52U;
  sbox1[73U] = (uint8_t)0x3bU;
  sbox1[74U] = (uint8_t)0xd6U;
  sbox1[75U] = (uint8_t)0xb3U;
  sbox1[76U] = (uint8_t)0x29U;
  sbox1[77U] = (uint8_t)0xe3U;
  sbox1[78U] = (uint8_t)0x2fU;
  sbox1[79U] = (uint8_t)0x84U;
  sbox1[80U] = (uint8_t)0x53U;
  sbox1[81U] = (uint8_t)0xd1U;
  sbox1[82U] = (uint8_t)0x00U;
  sbox1[83U] = (uint8_t)0xedU;
  sbox1[84U] = (uint8_t)0x20U;
  sbox1[85U] = (uint8_t)0xfcU;
  sbox1[86U] = (uint8_t)0xb1U;
  sbox1[87U] = (uint8_t)0x5bU;
  sbox1[88U] = (uint8_t)0x6aU;
  sbox1[89U] = (uint8_t)0xcbU;
  sbox1[90U] = (uint8_t)0xbeU;
  sbox1[91U] = (uint8_t)0x39U;
  sbox1[92U] = (uint8_t)0x4aU;
  sbox1[93U] = (uint8_t)0x4cU;
  sbox1[94U] = (uint8_t)0x58U;
  sbox1[95U] = (uint8_t)0xcfU;
  sbox1[96U] = (uint8_t)0xd0U;
  sbox1[97U] = (uint8_t)0xefU;
  sbox1[98U] = (uint8_t)0xaaU;
  sbox1[99U] = (uint8_t)0xfbU;
  sbox1[100U] = (uint8_t)0x43U;
  sbox1[101U] = (uint8_t)0x4dU;
  sbox1[102U] = (uint8_t)0x33U;
  sbox1[103U] = (uint8_t)0x85U;
  sbox1[104U] = (uint8_t)0x45U;
  sbox1[105U] = (uint8_t)0xf9U;
  sbox1[106U] = (uint8_t)0x02U;
  sbox1[107U] = (uint8_t)0x7fU;
  sbox1[108U] = (uint8_t)0x50U;
  sbox1[109U] = (uint8_t)0x3cU;
  sbox1[110U] = (uint8_t)0x9fU;
  sbox1[111U] = (uint8_t)0xa8U;
  sbox1[112U] = (uint8_t)0x51U;
  sbox1[113U] = (uint8_t)0xa3U;
  sbox1[114U] = (uint8_t)0x40U;
  sbox1[115U] = (uint8_t)0x8fU;
  sbox1[116U] = (uint8_t)0x92U;
  sbox1[117U] = (uint8_t)0x9dU;
  sbox1[118U] = (uint8_t)0x38U;
  sbox1[119U] = (uint8_t)0xf5U;
  sbox1[120U] = (uint8_t)0xbcU;
  sbox1[121U] = (uint8_t)0xb6U;
  sbox1[122U] = (uint8_t)0xdaU;
  sbox1[123U] = (uint8_t)0x21U;
  sbox1[124U] = (uint8_t)0x10U;
  sbox1[125U] = (uint8_t)0xffU;
  sbox1[126U] = (uint8_t)0xf3U;
  sbox1[127U] = (uint8_t)0xd2U;
  sbox1[128U] = (uint8_t)0xcdU;
  sbox1[129U] = (uint8_t)0x0cU;
  sbox1[130U] = (uint8_t)0x13U;
  sbox1[131U] = (uint8_t)0xecU;
  sbox1[132U] = (uint8_t)0x5fU;
  sbox1[133U] = (uint8_t)0x97U;
  sbox1[134U] = (uint8_t)0x44U;
  sbox1[135U] = (uint8_t)0x17U;
  sbox1[136U] = (uint8_t)0xc4U;
  sbox1[137U] = (uint8_t)0xa7U;
  sbox1[138U] = (uint8_t)0x7eU;
  sbox1[139U] = (uint8_t)0x3dU;
  sbox1[140U] = (uint8_t)0x64U;
  sbox1[141U] = (uint8_t)0x5dU;
  sbox1[142U] = (uint8_t)0x19U;
  sbox1[143U] = (uint8_t)0x73U;
  sbox1[144U] = (uint8_t)0x60U;
  sbox1[145U] = (uint8_t)0x81U;
  sbox1[146U] = (uint8_t)0x4fU;
  sbox1[147U] = (uint8_t)0xdcU;
  sbox1[148U] = (uint8_t)0x22U;
  sbox1[149U] = (uint8_t)0x2aU;
  sbox1[150U] = (uint8_t)0x90U;
  sbox1[151U] = (uint8_t)0x88U;
  sbox1[152U] = (uint8_t)0x46U;
  sbox1[153U] = (uint8_t)0xeeU;
  sbox1[154U] = (uint8_t)0xb8U;
  sbox1[155U] = (uint8_t)0x14U;
  sbox1[156U] = (uint8_t)0xdeU;
  sbox1[157U] = (uint8_t)0x5eU;
  sbox1[158U] = (uint8_t)0x0bU;
  sbox1[159U] = (uint8_t)0xdbU;
  sbox1[160U] = (uint8_t)0xe0U;
  sbox1[161U] = (uint8_t)0x32U;
  sbox1[162U] = (uint8_t)0x3aU;
  sbox1[163U] = (uint8_t)0x0aU;
  sbox1[164U] = (uint8_t)0x49U;
  sbox1[165U] = (uint8_t)0x06U;
  sbox1[166U] = (uint8_t)0x24U;
  sbox1[167U] = (uint8_t)0x5cU;
  sbox1[168U] = (uint8_t)0xc2U;
  sbox1[169U] = (uint8_t)0xd3U;
  sbox1[170U] = (uint8_t)0xacU;
  sbox1[171U] = (uint8_t)0x62U;
  sbox1[172U] = (uint8_t)0x91U;
  sbox1[173U] = (uint8_t)0x95U;
  sbox1[174U] = (uint8_t)0xe4U;
  sbox1[175U] = (uint8_t)0x79U;
  sbox1[176U] = (uint8_t)0xe7U;
  sbox1[177U] = (uint8_t)0xc8U;
  sbox1[178U] = (uint8_t)0x37U;
  sbox1[179U] = (uint8_t)0x6dU;
  sbox1[180U] = (uint8_t)0x8dU;
  sbox1[181U] = (uint8_t)0xd5U;
  sbox1[182U] = (uint8_t)0x4eU;
  sbox1[183U] = (uint8_t)0xa9U;
  sbox1[184U] = (uint8_t)0x6cU;
  sbox1[185U] = (uint8_t)0x56U;
  sbox1[186U] = (uint8_t)0xf4U;
  sbox1[187U] = (uint8_t)0xeaU;
  sbox1[188U] = (uint8_t)0x65U;
  sbox1[189U] = (uint8_t)0x7aU;
  sbox1[190U] = (uint8_t)0xaeU;
  sbox1[191U] = (uint8_t)0x08U;
  sbox1[192U] = (uint8_t)0xbaU;
  sbox1[193U] = (uint8_t)0x78U;
  sbox1[194U] = (uint8_t)0x25U;
  sbox1[195U] = (uint8_t)0x2eU;
  sbox1[196U] = (uint8_t)0x1cU;
  sbox1[197U] = (uint8_t)0xa6U;
  sbox1[198U] = (uint8_t)0xb4U;
  sbox1[199U] = (uint8_t)0xc6U;
  sbox1[200U] = (uint8_t)0xe8U;
  sbox1[201U] = (uint8_t)0xddU;
  sbox1[202U] = (uint8_t)0x74U;
  sbox1[203U] = (uint8_t)0x1fU;
  sbox1[204U] = (uint8_t)0x4bU;
  sbox1[205U] = (uint8_t)0xbdU;
  sbox1[206U] = (uint8_t)0x8bU;
  sbox1[207U] = (uint8_t)0x8aU;
  sbox1[208U] = (uint8_t)0x70U;
  sbox1[209U] = (uint8_t)0x3eU;
  sbox1[210U] = (uint8_t)0xb5U;
  sbox1[211U] = (uint8_t)0x66U;
  sbox1[212U] = (uint8_t)0x48U;
  sbox1[213U] = (uint8_t)0x03U;
  sbox1[214U] = (uint8_t)0xf6U;
  sbox1[215U] = (uint8_t)0x0eU;
  sbox1[216U] = (uint8_t)0x61U;
  sbox1[217U] = (uint8_t)0x35U;
  sbox1[218U] = (uint8_t)0x57U;
  sbox1[219U] = (uint8_t)0xb9U;
  sbox1[220U] = (uint8_t)0x86U;
  sbox1[221U] = (uint8_t)0xc1U;
  sbox1[222U] = (uint8_t)0x1dU;
  sbox1[223U] = (uint8_t)0x9eU;
  sbox1[224U] = (uint8_t)0xe1U;
  sbox1[225U] = (uint8_t)0xf8U;
  sbox1[226U] = (uint8_t)0x98U;
  sbox1[227U] = (uint8_t)0x11U;
  sbox1[228U] = (uint8_t)0x69U;
  sbox1[229U] = (uint8_t)0xd9U;
  sbox1[230U] = (uint8_t)0x8eU;
  sbox1[231U] = (uint8_t)0x94U;
  sbox1[232U] = (uint8_t)0x9bU;
  sbox1[233U] = (uint8_t)0x1eU;
  sbox1[234U] = (uint8_t)0x87U;
  sbox1[235U] = (uint8_t)0xe9U;
  sbox1[236U] = (uint8_t)0xceU;
  sbox1[237U] = (uint8_t)0x55U;
  sbox1[238U] = (uint8_t)0x28U;
  sbox1[239U] = (uint8_t)0xdfU;
  sbox1[240U] = (uint8_t)0x8cU;
  sbox1[241U] = (uint8_t)0xa1U;
  sbox1[242U] = (uint8_t)0x89U;
  sbox1[243U] = (uint8_t)0x0dU;
  sbox1[244U] = (uint8_t)0xbfU;
  sbox1[245U] = (uint8_t)0xe6U;
  sbox1[246U] = (uint8_t)0x42U;
  sbox1[247U] = (uint8_t)0x68U;
  sbox1[248U] = (uint8_t)0x41U;
  sbox1[249U] = (uint8_t)0x99U;
  sbox1[250U] = (uint8_t)0x2dU;
  sbox1[251U] = (uint8_t)0x0fU;
  sbox1[252U] = (uint8_t)0xb0U;
  sbox1[253U] = (uint8_t)0x54U;
  sbox1[254U] = (uint8_t)0xbbU;
  sbox1[255U] = (uint8_t)0x16U;
}

void Crypto_Symmetric_AES128_mk_inv_sbox(uint8_t *sbox1)
{
  sbox1[0U] = (uint8_t)0x52U;
  sbox1[1U] = (uint8_t)0x09U;
  sbox1[2U] = (uint8_t)0x6aU;
  sbox1[3U] = (uint8_t)0xd5U;
  sbox1[4U] = (uint8_t)0x30U;
  sbox1[5U] = (uint8_t)0x36U;
  sbox1[6U] = (uint8_t)0xa5U;
  sbox1[7U] = (uint8_t)0x38U;
  sbox1[8U] = (uint8_t)0xbfU;
  sbox1[9U] = (uint8_t)0x40U;
  sbox1[10U] = (uint8_t)0xa3U;
  sbox1[11U] = (uint8_t)0x9eU;
  sbox1[12U] = (uint8_t)0x81U;
  sbox1[13U] = (uint8_t)0xf3U;
  sbox1[14U] = (uint8_t)0xd7U;
  sbox1[15U] = (uint8_t)0xfbU;
  sbox1[16U] = (uint8_t)0x7cU;
  sbox1[17U] = (uint8_t)0xe3U;
  sbox1[18U] = (uint8_t)0x39U;
  sbox1[19U] = (uint8_t)0x82U;
  sbox1[20U] = (uint8_t)0x9bU;
  sbox1[21U] = (uint8_t)0x2fU;
  sbox1[22U] = (uint8_t)0xffU;
  sbox1[23U] = (uint8_t)0x87U;
  sbox1[24U] = (uint8_t)0x34U;
  sbox1[25U] = (uint8_t)0x8eU;
  sbox1[26U] = (uint8_t)0x43U;
  sbox1[27U] = (uint8_t)0x44U;
  sbox1[28U] = (uint8_t)0xc4U;
  sbox1[29U] = (uint8_t)0xdeU;
  sbox1[30U] = (uint8_t)0xe9U;
  sbox1[31U] = (uint8_t)0xcbU;
  sbox1[32U] = (uint8_t)0x54U;
  sbox1[33U] = (uint8_t)0x7bU;
  sbox1[34U] = (uint8_t)0x94U;
  sbox1[35U] = (uint8_t)0x32U;
  sbox1[36U] = (uint8_t)0xa6U;
  sbox1[37U] = (uint8_t)0xc2U;
  sbox1[38U] = (uint8_t)0x23U;
  sbox1[39U] = (uint8_t)0x3dU;
  sbox1[40U] = (uint8_t)0xeeU;
  sbox1[41U] = (uint8_t)0x4cU;
  sbox1[42U] = (uint8_t)0x95U;
  sbox1[43U] = (uint8_t)0x0bU;
  sbox1[44U] = (uint8_t)0x42U;
  sbox1[45U] = (uint8_t)0xfaU;
  sbox1[46U] = (uint8_t)0xc3U;
  sbox1[47U] = (uint8_t)0x4eU;
  sbox1[48U] = (uint8_t)0x08U;
  sbox1[49U] = (uint8_t)0x2eU;
  sbox1[50U] = (uint8_t)0xa1U;
  sbox1[51U] = (uint8_t)0x66U;
  sbox1[52U] = (uint8_t)0x28U;
  sbox1[53U] = (uint8_t)0xd9U;
  sbox1[54U] = (uint8_t)0x24U;
  sbox1[55U] = (uint8_t)0xb2U;
  sbox1[56U] = (uint8_t)0x76U;
  sbox1[57U] = (uint8_t)0x5bU;
  sbox1[58U] = (uint8_t)0xa2U;
  sbox1[59U] = (uint8_t)0x49U;
  sbox1[60U] = (uint8_t)0x6dU;
  sbox1[61U] = (uint8_t)0x8bU;
  sbox1[62U] = (uint8_t)0xd1U;
  sbox1[63U] = (uint8_t)0x25U;
  sbox1[64U] = (uint8_t)0x72U;
  sbox1[65U] = (uint8_t)0xf8U;
  sbox1[66U] = (uint8_t)0xf6U;
  sbox1[67U] = (uint8_t)0x64U;
  sbox1[68U] = (uint8_t)0x86U;
  sbox1[69U] = (uint8_t)0x68U;
  sbox1[70U] = (uint8_t)0x98U;
  sbox1[71U] = (uint8_t)0x16U;
  sbox1[72U] = (uint8_t)0xd4U;
  sbox1[73U] = (uint8_t)0xa4U;
  sbox1[74U] = (uint8_t)0x5cU;
  sbox1[75U] = (uint8_t)0xccU;
  sbox1[76U] = (uint8_t)0x5dU;
  sbox1[77U] = (uint8_t)0x65U;
  sbox1[78U] = (uint8_t)0xb6U;
  sbox1[79U] = (uint8_t)0x92U;
  sbox1[80U] = (uint8_t)0x6cU;
  sbox1[81U] = (uint8_t)0x70U;
  sbox1[82U] = (uint8_t)0x48U;
  sbox1[83U] = (uint8_t)0x50U;
  sbox1[84U] = (uint8_t)0xfdU;
  sbox1[85U] = (uint8_t)0xedU;
  sbox1[86U] = (uint8_t)0xb9U;
  sbox1[87U] = (uint8_t)0xdaU;
  sbox1[88U] = (uint8_t)0x5eU;
  sbox1[89U] = (uint8_t)0x15U;
  sbox1[90U] = (uint8_t)0x46U;
  sbox1[91U] = (uint8_t)0x57U;
  sbox1[92U] = (uint8_t)0xa7U;
  sbox1[93U] = (uint8_t)0x8dU;
  sbox1[94U] = (uint8_t)0x9dU;
  sbox1[95U] = (uint8_t)0x84U;
  sbox1[96U] = (uint8_t)0x90U;
  sbox1[97U] = (uint8_t)0xd8U;
  sbox1[98U] = (uint8_t)0xabU;
  sbox1[99U] = (uint8_t)0x00U;
  sbox1[100U] = (uint8_t)0x8cU;
  sbox1[101U] = (uint8_t)0xbcU;
  sbox1[102U] = (uint8_t)0xd3U;
  sbox1[103U] = (uint8_t)0x0aU;
  sbox1[104U] = (uint8_t)0xf7U;
  sbox1[105U] = (uint8_t)0xe4U;
  sbox1[106U] = (uint8_t)0x58U;
  sbox1[107U] = (uint8_t)0x05U;
  sbox1[108U] = (uint8_t)0xb8U;
  sbox1[109U] = (uint8_t)0xb3U;
  sbox1[110U] = (uint8_t)0x45U;
  sbox1[111U] = (uint8_t)0x06U;
  sbox1[112U] = (uint8_t)0xd0U;
  sbox1[113U] = (uint8_t)0x2cU;
  sbox1[114U] = (uint8_t)0x1eU;
  sbox1[115U] = (uint8_t)0x8fU;
  sbox1[116U] = (uint8_t)0xcaU;
  sbox1[117U] = (uint8_t)0x3fU;
  sbox1[118U] = (uint8_t)0x0fU;
  sbox1[119U] = (uint8_t)0x02U;
  sbox1[120U] = (uint8_t)0xc1U;
  sbox1[121U] = (uint8_t)0xafU;
  sbox1[122U] = (uint8_t)0xbdU;
  sbox1[123U] = (uint8_t)0x03U;
  sbox1[124U] = (uint8_t)0x01U;
  sbox1[125U] = (uint8_t)0x13U;
  sbox1[126U] = (uint8_t)0x8aU;
  sbox1[127U] = (uint8_t)0x6bU;
  sbox1[128U] = (uint8_t)0x3aU;
  sbox1[129U] = (uint8_t)0x91U;
  sbox1[130U] = (uint8_t)0x11U;
  sbox1[131U] = (uint8_t)0x41U;
  sbox1[132U] = (uint8_t)0x4fU;
  sbox1[133U] = (uint8_t)0x67U;
  sbox1[134U] = (uint8_t)0xdcU;
  sbox1[135U] = (uint8_t)0xeaU;
  sbox1[136U] = (uint8_t)0x97U;
  sbox1[137U] = (uint8_t)0xf2U;
  sbox1[138U] = (uint8_t)0xcfU;
  sbox1[139U] = (uint8_t)0xceU;
  sbox1[140U] = (uint8_t)0xf0U;
  sbox1[141U] = (uint8_t)0xb4U;
  sbox1[142U] = (uint8_t)0xe6U;
  sbox1[143U] = (uint8_t)0x73U;
  sbox1[144U] = (uint8_t)0x96U;
  sbox1[145U] = (uint8_t)0xacU;
  sbox1[146U] = (uint8_t)0x74U;
  sbox1[147U] = (uint8_t)0x22U;
  sbox1[148U] = (uint8_t)0xe7U;
  sbox1[149U] = (uint8_t)0xadU;
  sbox1[150U] = (uint8_t)0x35U;
  sbox1[151U] = (uint8_t)0x85U;
  sbox1[152U] = (uint8_t)0xe2U;
  sbox1[153U] = (uint8_t)0xf9U;
  sbox1[154U] = (uint8_t)0x37U;
  sbox1[155U] = (uint8_t)0xe8U;
  sbox1[156U] = (uint8_t)0x1cU;
  sbox1[157U] = (uint8_t)0x75U;
  sbox1[158U] = (uint8_t)0xdfU;
  sbox1[159U] = (uint8_t)0x6eU;
  sbox1[160U] = (uint8_t)0x47U;
  sbox1[161U] = (uint8_t)0xf1U;
  sbox1[162U] = (uint8_t)0x1aU;
  sbox1[163U] = (uint8_t)0x71U;
  sbox1[164U] = (uint8_t)0x1dU;
  sbox1[165U] = (uint8_t)0x29U;
  sbox1[166U] = (uint8_t)0xc5U;
  sbox1[167U] = (uint8_t)0x89U;
  sbox1[168U] = (uint8_t)0x6fU;
  sbox1[169U] = (uint8_t)0xb7U;
  sbox1[170U] = (uint8_t)0x62U;
  sbox1[171U] = (uint8_t)0x0eU;
  sbox1[172U] = (uint8_t)0xaaU;
  sbox1[173U] = (uint8_t)0x18U;
  sbox1[174U] = (uint8_t)0xbeU;
  sbox1[175U] = (uint8_t)0x1bU;
  sbox1[176U] = (uint8_t)0xfcU;
  sbox1[177U] = (uint8_t)0x56U;
  sbox1[178U] = (uint8_t)0x3eU;
  sbox1[179U] = (uint8_t)0x4bU;
  sbox1[180U] = (uint8_t)0xc6U;
  sbox1[181U] = (uint8_t)0xd2U;
  sbox1[182U] = (uint8_t)0x79U;
  sbox1[183U] = (uint8_t)0x20U;
  sbox1[184U] = (uint8_t)0x9aU;
  sbox1[185U] = (uint8_t)0xdbU;
  sbox1[186U] = (uint8_t)0xc0U;
  sbox1[187U] = (uint8_t)0xfeU;
  sbox1[188U] = (uint8_t)0x78U;
  sbox1[189U] = (uint8_t)0xcdU;
  sbox1[190U] = (uint8_t)0x5aU;
  sbox1[191U] = (uint8_t)0xf4U;
  sbox1[192U] = (uint8_t)0x1fU;
  sbox1[193U] = (uint8_t)0xddU;
  sbox1[194U] = (uint8_t)0xa8U;
  sbox1[195U] = (uint8_t)0x33U;
  sbox1[196U] = (uint8_t)0x88U;
  sbox1[197U] = (uint8_t)0x07U;
  sbox1[198U] = (uint8_t)0xc7U;
  sbox1[199U] = (uint8_t)0x31U;
  sbox1[200U] = (uint8_t)0xb1U;
  sbox1[201U] = (uint8_t)0x12U;
  sbox1[202U] = (uint8_t)0x10U;
  sbox1[203U] = (uint8_t)0x59U;
  sbox1[204U] = (uint8_t)0x27U;
  sbox1[205U] = (uint8_t)0x80U;
  sbox1[206U] = (uint8_t)0xecU;
  sbox1[207U] = (uint8_t)0x5fU;
  sbox1[208U] = (uint8_t)0x60U;
  sbox1[209U] = (uint8_t)0x51U;
  sbox1[210U] = (uint8_t)0x7fU;
  sbox1[211U] = (uint8_t)0xa9U;
  sbox1[212U] = (uint8_t)0x19U;
  sbox1[213U] = (uint8_t)0xb5U;
  sbox1[214U] = (uint8_t)0x4aU;
  sbox1[215U] = (uint8_t)0x0dU;
  sbox1[216U] = (uint8_t)0x2dU;
  sbox1[217U] = (uint8_t)0xe5U;
  sbox1[218U] = (uint8_t)0x7aU;
  sbox1[219U] = (uint8_t)0x9fU;
  sbox1[220U] = (uint8_t)0x93U;
  sbox1[221U] = (uint8_t)0xc9U;
  sbox1[222U] = (uint8_t)0x9cU;
  sbox1[223U] = (uint8_t)0xefU;
  sbox1[224U] = (uint8_t)0xa0U;
  sbox1[225U] = (uint8_t)0xe0U;
  sbox1[226U] = (uint8_t)0x3bU;
  sbox1[227U] = (uint8_t)0x4dU;
  sbox1[228U] = (uint8_t)0xaeU;
  sbox1[229U] = (uint8_t)0x2aU;
  sbox1[230U] = (uint8_t)0xf5U;
  sbox1[231U] = (uint8_t)0xb0U;
  sbox1[232U] = (uint8_t)0xc8U;
  sbox1[233U] = (uint8_t)0xebU;
  sbox1[234U] = (uint8_t)0xbbU;
  sbox1[235U] = (uint8_t)0x3cU;
  sbox1[236U] = (uint8_t)0x83U;
  sbox1[237U] = (uint8_t)0x53U;
  sbox1[238U] = (uint8_t)0x99U;
  sbox1[239U] = (uint8_t)0x61U;
  sbox1[240U] = (uint8_t)0x17U;
  sbox1[241U] = (uint8_t)0x2bU;
  sbox1[242U] = (uint8_t)0x04U;
  sbox1[243U] = (uint8_t)0x7eU;
  sbox1[244U] = (uint8_t)0xbaU;
  sbox1[245U] = (uint8_t)0x77U;
  sbox1[246U] = (uint8_t)0xd6U;
  sbox1[247U] = (uint8_t)0x26U;
  sbox1[248U] = (uint8_t)0xe1U;
  sbox1[249U] = (uint8_t)0x69U;
  sbox1[250U] = (uint8_t)0x14U;
  sbox1[251U] = (uint8_t)0x63U;
  sbox1[252U] = (uint8_t)0x55U;
  sbox1[253U] = (uint8_t)0x21U;
  sbox1[254U] = (uint8_t)0x0cU;
  sbox1[255U] = (uint8_t)0x7dU;
}

#ifdef _MSC_VER
// Work around a /Ox code-gen bug in AES key expansion, in the MSVC compiler
#pragma optimize("", off)
#pragma optimize("s", on)
#endif

static uint8_t access0(uint8_t *sbox1, uint8_t i)
{
  return sbox1[(uint32_t)i];
}

#ifdef _MSC_VER
#pragma optimize("", on)
#endif

static void subBytes_aux_sbox0(uint8_t *state, uint8_t *sbox1, uint32_t ctr)
{
  if (ctr != (uint32_t)16U)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access0(sbox1, si);
    state[ctr] = si_;
    subBytes_aux_sbox0(state, sbox1, ctr + (uint32_t)1U);
  }
}

static void subBytes_sbox0(uint8_t *state, uint8_t *sbox1)
{
  subBytes_aux_sbox0(state, sbox1, (uint32_t)0U);
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

static void cipher_loop0(uint8_t *state, uint8_t *w, uint8_t *sbox1, uint32_t round)
{
  if (round != (uint32_t)10U)
  {
    subBytes_sbox0(state, sbox1);
    shiftRows0(state);
    mixColumns0(state);
    addRoundKey0(state, w, round);
    cipher_loop0(state, w, sbox1, round + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES128_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (uint8_t));
  addRoundKey0(state, w, (uint32_t)0U);
  cipher_loop0(state, w, sbox1, (uint32_t)1U);
  subBytes_sbox0(state, sbox1);
  shiftRows0(state);
  addRoundKey0(state, w, (uint32_t)10U);
  memcpy(out, state, (uint32_t)16U * sizeof (uint8_t));
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

static void subWord0(uint8_t *word, uint8_t *sbox1)
{
  word[0U] = access0(sbox1, word[0U]);
  word[1U] = access0(sbox1, word[1U]);
  word[2U] = access0(sbox1, word[2U]);
  word[3U] = access0(sbox1, word[3U]);
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

static void keyExpansion_aux_00(uint8_t *w, uint8_t *temp, uint8_t *sbox1, uint32_t j)
{
  memcpy(temp, w + (uint32_t)4U * j - (uint32_t)4U, (uint32_t)4U * sizeof (uint8_t));
  if (j % (uint32_t)4U == (uint32_t)0U)
  {
    rotWord0(temp);
    subWord0(temp, sbox1);
    uint8_t t0 = temp[0U];
    uint8_t rc = rcon0(j / (uint32_t)4U, (uint8_t)1U);
    uint8_t z = t0 ^ rc;
    temp[0U] = z;
  }
  else if (j % (uint32_t)4U == (uint32_t)4U)
  {
    subWord0(temp, sbox1);
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

static void keyExpansion_aux0(uint8_t *w, uint8_t *temp, uint8_t *sbox1, uint32_t j)
{
  if (j < (uint32_t)44U)
  {
    keyExpansion_aux_00(w, temp, sbox1, j);
    keyExpansion_aux_10(w, temp, j);
    keyExpansion_aux0(w, temp, sbox1, j + (uint32_t)1U);
  }
}

void Crypto_Symmetric_AES128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox1)
{
  uint8_t temp[4U] = { 0U };
  memcpy(w, key, (uint32_t)16U * sizeof (uint8_t));
  keyExpansion_aux0(w, temp, sbox1, (uint32_t)4U);
}

static void invSubBytes_aux_sbox0(uint8_t *state, uint8_t *sbox1, uint32_t ctr)
{
  if (!(ctr == (uint32_t)16U))
  {
    uint8_t si = state[ctr];
    uint8_t si_ = access0(sbox1, si);
    state[ctr] = si_;
    invSubBytes_aux_sbox0(state, sbox1, ctr + (uint32_t)1U);
  }
}

static void invSubBytes_sbox0(uint8_t *state, uint8_t *sbox1)
{
  invSubBytes_aux_sbox0(state, sbox1, (uint32_t)0U);
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

static void inv_cipher_loop0(uint8_t *state, uint8_t *w, uint8_t *sbox1, uint32_t round)
{
  if (round != (uint32_t)0U)
  {
    invShiftRows0(state);
    invSubBytes_sbox0(state, sbox1);
    addRoundKey0(state, w, round);
    invMixColumns0(state);
    inv_cipher_loop0(state, w, sbox1, round - (uint32_t)1U);
  }
}

void
Crypto_Symmetric_AES128_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox1)
{
  uint8_t state[16U] = { 0U };
  memcpy(state, input, (uint32_t)16U * sizeof (uint8_t));
  addRoundKey0(state, w, (uint32_t)10U);
  inv_cipher_loop0(state, w, sbox1, (uint32_t)9U);
  invShiftRows0(state);
  invSubBytes_sbox0(state, sbox1);
  addRoundKey0(state, w, (uint32_t)0U);
  memcpy(out, state, (uint32_t)16U * sizeof (uint8_t));
}

