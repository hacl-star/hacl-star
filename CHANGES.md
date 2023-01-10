# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Each change begins with a version (if applicable) and a timestamp, and then a set of changes, categorized by type:
- Added for new features.
- Changed for changes in existing functionality.
- Deprecated for soon-to-be removed features.
- Removed for now removed features.
- Fixed for any bug fixes.
- Security in case of vulnerabilities.


## 2022-12-19

- Added JS bindings for secp256k1
- Added an OCaml API for secp256k1

## 2022-12-14

- Align the APIs in Hacl_Hash_SHA2 and Hacl_Streaming_SHA2 for full hashes. The
  latter now observes the argument order of the former.

## 2022-12-07

- Added secret_to_public for secp256k1

## 2022-12-06

- Tighten the `EverCrypt_Hash` header file to only expose the one-shot and
  "streaming" APIs.

## 2022-12-01

### Added

- Initialized CHANGES.md file with changelog template
