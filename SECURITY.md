# Security Policy

## Verification 

The main branch contains the latest verified code for the HACL* library and includes some unverified C code for low-level platform features such as compiler intrinsics for SIMD instructions. All this code is routinely tested on several platforms, but it is quite possible that our unverified code makes incorrect assumptions and/or fails. Furthermore, HACL* only protects against remote timing attacks and so it is possible that there are side-channel leaks in the compiled code. To better understand the verification guarantees, see https://hacl-star.github.io/Overview.html#what-is-verified-software. We welcome any security reports on this library and commit to fixing them as soon as possible.

## Reporting a Vulnerability

Please use the GitHub [private vulnerability reporting](https://docs.github.com/en/code-security/security-advisories/guidance-on-reporting-and-writing/privately-reporting-a-security-vulnerability) feature. 
