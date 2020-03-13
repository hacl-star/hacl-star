var my_print = console.log;

(function() {
  'use strict';
  var isInitialized = false
  var HaclWasm = {}

  // This object is passed at the wasm instantiation to link the missing
  // `random_bytes` function, needed for generating new keyPairs.
  var my_imports = {}

  const checkIfInitialized = function() {
    if (isInitialized === false) {
      return Promise.all(my_modules.map(m => {
        return fetch("../" + m + ".wasm")
      })).then(responses =>
        Promise.all(responses.map(r => r.arrayBuffer()))
      ).then(bufs => {
        return link(my_imports, bufs.map((b, i) => ({
          buf: b,
          name: my_modules[i]
        })))
      }).then(scope => {
        HaclWasm = scope;
        isInitialized = true;
        console.log("DEBUG: HaclWasm:", HaclWasm);
      })
    } else {
      return Promise.resolve()
    }
  }

  /*
  Inside WebAssembly, the functions only take pointers to memory and integers.
  However, we want to expose the functions of the wasm module with a nice Javascript
  API that manipulates ArrayBuffers.

  In order to do that, we have to describe the Javascript prototype of each function
  that we expose. The functions can take and return multiple objects that can be
  buffers, integers or booleans. The buffers can either have a fixed length (and
  in that case we check dynamically whether they have the correct length), or
  have a variable length (and we have to pass that length as an additional
  parameter to WebAssembly).

  In order to match the Javascript API with the actual calls to WebAssembly functions,
  we make several assumptions on the functions exposed in the WebAssembly generated
  from Low*:
  - each variable length buffer argument is preceded by an additional argument,
    its length;
  - output buffers are always first in the list of arguments;
  - if the Javascript function returns a variable length buffer, then the Low* function
    should always return the length of the buffer as an integer.

  For functions that return a variable length buffer, the prototype has to be
  initialized before each call with the maximum output length (that can
  depend on some input variables).
  */

  const Signatures = {
    "Curve25519_51": {
      "ecdh": {
        "mpdule": "Hacl_Curve25519_51",
        "name": "ecdh",
        "input_args": [{
            "type": "buffer",
            "size": 32
          },
          {
            "type": "buffer",
            "size": 32
          }
        ],
        "output_args": [{
          "type": "buffer",
          "size": 32
        }],
        "return": [{
          "type": "bool"
        }],

      }
    }
  }

  //
  // const FStarVerifySig = {
  //   "module": "Impl_Signal_Core",
  //   "name": "verify_sig",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 64
  //     }
  //   ],
  //   "return": [{
  //     "type": "bool"
  //   }]
  // }
  //
  // const FStarSign = {
  //   "module": "Impl_Signal_Core",
  //   "name": "sign0",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 64
  //   }, ]
  //
  // }
  //
  // const FStarRatchet = {
  //   "module": "Impl_Signal_Core",
  //   "name": "ratchet",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     }
  //   ],
  //   "return": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     }
  //   ]
  // }
  //
  // const FStarInitiate = {
  //   "module": "Impl_Signal_Core",
  //   "name": "initiate",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "bool"
  //     }
  //   ],
  //   "return": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     }
  //   ]
  // }
  //
  // const FStarRespond = {
  //   "module": "Impl_Signal_Core",
  //   "name": "respond",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "bool"
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 32
  //   }, ]
  // }
  //
  // const FStarFillMessageKeys = {
  //   "module": "Impl_Signal_Core",
  //   "name": "fill_message_keys",
  //   "args": [{
  //     "type": "buffer",
  //     "size": 32
  //   }, ],
  //   "return": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //   ]
  // }
  //
  // const FStarEncrypt = function(maxOutputSize) {
  //   return {
  //     "module": "Impl_Signal_Core",
  //     "name": "encrypt",
  //     "args": [{
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 32
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "integer"
  //       },
  //       {
  //         "type": "integer"
  //       },
  //       {
  //         "type": "varbuf"
  //       },
  //     ],
  //     "return": [{
  //       "type": "varbuf",
  //       "size": maxOutputSize
  //     }, ]
  //   };
  // }
  //
  // const FStarDecrypt = function(maxOutputSize) {
  //   return {
  //     "module": "Impl_Signal_Core",
  //     "name": "decrypt",
  //     "args": [{
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 33
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 32
  //       },
  //       {
  //         "type": "integer"
  //       },
  //       {
  //         "type": "integer"
  //       },
  //       {
  //         "type": "varbuf"
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 8
  //       },
  //     ],
  //     "return": [{
  //       "type": "varbuf",
  //       "size": maxOutputSize
  //     }, ]
  //   };
  // }
  //
  // const FStarAESEnc = function(maxOutputSize) {
  //   return {
  //     "module": "Impl_Signal_Crypto",
  //     "name": "enc_standalone",
  //     "args": [{
  //         "type": "buffer",
  //         "size": 32
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 16
  //       },
  //       {
  //         "type": "varbuf"
  //       },
  //     ],
  //     "return": [{
  //       "type": "varbuf",
  //       "size": maxOutputSize
  //     }, ]
  //   }
  // }
  //
  // const FStarAESDec = function(maxOutputSize) {
  //   return {
  //     "module": "Impl_Signal_Crypto",
  //     "name": "dec_standalone",
  //     "args": [{
  //         "type": "buffer",
  //         "size": 32
  //       },
  //       {
  //         "type": "buffer",
  //         "size": 16
  //       },
  //       {
  //         "type": "varbuf"
  //       },
  //     ],
  //     "return": [{
  //       "type": "varbuf",
  //       "size": maxOutputSize
  //     }, ]
  //   }
  // }
  //
  // const FStarHMAC = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "hmac_standalone",
  //   "args": [{
  //       "type": "varbuf"
  //     },
  //     {
  //       "type": "varbuf"
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 32
  //   }, ]
  //
  // }
  //
  // const FStarSHA512 = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "hash_sha512",
  //   "args": [{
  //     "type": "varbuf"
  //   }, ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 64
  //   }, ]
  //
  // }
  //
  // const FStarHKDF = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "hkdf_standalone",
  //   "args": [{
  //       "type": "varbuf"
  //     },
  //     {
  //       "type": "varbuf"
  //     },
  //     {
  //       "type": "varbuf"
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 96
  //   }, ]
  //
  // }
  //
  // const FStarGenerateKeyPair = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "sign",
  //   "args": [],
  //   "return": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //   ]
  // }
  //
  // const FStarEd25519Sign = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "curve25519_sign_modified",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "varbuf"
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 64
  //   }, ]
  // }
  //
  // const FStarEd25519Verify = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "verify",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 64
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 33
  //     },
  //     {
  //       "type": "varbuf"
  //     },
  //   ],
  //   "return": [{
  //     "type": "bool"
  //   }]
  // }
  //
  // const FStarECDHE = {
  //   "module": "Impl_Signal_Crypto",
  //   "name": "ecdhe",
  //   "args": [{
  //       "type": "buffer",
  //       "size": 32
  //     },
  //     {
  //       "type": "buffer",
  //       "size": 32
  //     },
  //   ],
  //   "return": [{
  //     "type": "buffer",
  //     "size": 32
  //   }, ]
  // }



  const CheckIfByteArray = function(candidate, length, name) {
    if (!(typeof(candidate) === "object") ||
      !(candidate.length === length) ||
      !(candidate.constructor === Uint8Array)
    ) {
      throw new Error(
        "name: Please ensure the argument is a " + length + "-bytes Uint8Array."
      );
    }
  };

  const malloc_array = function(array) {
    let pointer = reserve(HaclWasm.Kremlin.mem, array.length);
    let memory = new Uint8Array(HaclWasm.Kremlin.mem.buffer);
    for (let i = 0; i < array.length; i++) {
      memory[pointer + i] = array[i];
    }
    return pointer;
  };

  const read_memory = function(ptr, len) {
    var result = new ArrayBuffer(len);
    (new Uint8Array(result).set(new Uint8Array(HaclWasm.Kremlin.mem.buffer)
      .subarray(ptr, ptr + len)));
    return new Uint8Array(result);
  };

  const callWithProto = function(proto, args) {
    if (args.length != proto.args.length) {
      throw Error("wrong number of arguments to call the FStar function !")
    }
    let memory = new Uint32Array(HaclWasm.Kremlin.mem.buffer);
    let sp = memory[0];
    let args_pointers = args.flatMap((arg, i) => {
      let protoArg = proto.args[i];
      if (protoArg.type === "buffer") {
        let argByteBuffer = new Uint8Array(arg);
        CheckIfByteArray(argByteBuffer, protoArg.size, proto.name);
        let pointer = malloc_array(argByteBuffer);
        return [{
          "value": pointer,
          "index": i
        }];
      }
      if (protoArg.type === "varbuf") {
        let argByteBuffer = new Uint8Array(arg);
        CheckIfByteArray(argByteBuffer, argByteBuffer.byteLength, proto.name);
        let pointer = malloc_array(argByteBuffer);
        return [{
            "value": argByteBuffer.byteLength,
            "index": null
          },
          {
            "value": pointer,
            "index": i
          }
        ];
      }
      if (protoArg.type === "bool" || protoArg.type === "integer") {
        return [{
          "value": arg,
          "index": i
        }];
      }
      throw Error("Unimplemented !");
    });
    let return_pointers = proto.return.filter(ret => {
      return ret.type == "buffer" || ret.type == "varbuf"
    }).flatMap((ret, i) => {
      let byteBuffer = new Uint8Array(new ArrayBuffer(ret.size));
      let pointer = malloc_array(byteBuffer);
      if (ret.type == "varbuf") {
        return [{
            "value": ret.size,
            "index": null
          },
          {
            "value": pointer,
            "index": i
          }
        ]
      } else {
        return [{
          "value": pointer,
          "index": i
        }];
      }
    });
    let call_return = HaclWasm[proto.module][proto.name](
      ...return_pointers.concat(args_pointers).map(x => {
        return x.value;
      })
    );
    let return_buffers = return_pointers.filter(pointer => {
      return pointer.index !== null
    }).map((pointer, i) => {
      let protoRet = proto.return[pointer.index];
      var size;
      if (protoRet.type == "buffer") {
        size = protoRet.size;
      } else {
        size = call_return;
      }
      let retBuf = new ArrayBuffer(size);
      (new Uint8Array(retBuf)).set(read_memory(pointer.value, size))
      return retBuf;
    });
    memory[0] = sp;
    if (proto.return.length === 1) {
      if (proto.return[0].type === "bool") {
        return call_return === 1;
      }
      if (proto.return[0].type === "integer") {
        return call_return;
      }
      if (proto.return[0].type === "buffer" || proto.return[0].type === "varbuf") {
        return return_buffers[0];
      }
    } else {
      return return_buffers;
    }
  }




  async function SignalCoreVerifySig(identityKey, signedPublicKey, signature) {
    await checkIfInitialized();
    let res = callWithProto(FStarVerifySig, [identityKey, signedPublicKey, signature]);
    if (res !== true) {
      throw new Error("Invalid signature");
    }
  }

  async function SignalCoreSign(privKey, pubKey) {
    await checkIfInitialized();
    let res = callWithProto(FStarSign, [privKey, pubKey]);
    return res;
  }

  function SignalCoreGenerateRegistrationId() {
    var registrationId = new Uint16Array(Internal.crypto.getRandomBytes(2))[0];
    return registrationId & 0x3fff;
  }

  async function SignalCoreCreateKeyPair(privKey) {
    if (privKey === undefined) {
      privKey = Internal.crypto.getRandomBytes(32);
    }
    return Internal.Curve.async.createKeyPair(privKey);
  }


  async function SignalCoreRatchet(
    rootKey,
    ourEphemeralPrivKey,
    theirEphemeralPubKey
  ) {
    await checkIfInitialized();
    return callWithProto(FStarRatchet, [rootKey, ourEphemeralPrivKey, theirEphemeralPubKey]);
  }

  async function SignalCoreInitiate(
    ourIdentityPrivKey,
    basePrivKey,
    ourOneTimePrivKey,
    theirIdentityPubKey,
    theirSignedPubKey,
    theirOneTimePubKey,
    definedTheirOnetimePubKey
  ) {
    await checkIfInitialized();
    return callWithProto(FStarInitiate, [
      ourIdentityPrivKey,
      basePrivKey,
      ourOneTimePrivKey,
      theirIdentityPubKey,
      theirSignedPubKey,
      theirOneTimePubKey,
      definedTheirOnetimePubKey
    ]);
  }

  async function SignalCoreRespond(
    ourIdentityPrivKey,
    ourSignedPrivKey,
    ourOnetimePrivKey,
    definedOurOnetimePrivKey,
    theirIdentityPubKey,
    theirOnetimePubKey
  ) {
    await checkIfInitialized();
    return callWithProto(FStarRespond, [
      ourIdentityPrivKey,
      ourSignedPrivKey,
      ourOnetimePrivKey,
      definedOurOnetimePrivKey,
      theirIdentityPubKey,
      theirOnetimePubKey
    ])
  }

  async function SignalCoreFillMessagesKeys(chainKey) {
    await checkIfInitialized();
    return callWithProto(FStarFillMessageKeys, [
      chainKey
    ]);
  }

  async function SignalCoreEncrypt(
    ourIdentityPubKey,
    theirIdentityPubKey,
    msgKey,
    ourEphemeralPubKey,
    previousCounter,
    counter,
    buffer,
  ) {
    await checkIfInitialized();
    return callWithProto(FStarEncrypt(buffer.byteLength + 82), [
      ourIdentityPubKey,
      theirIdentityPubKey,
      msgKey,
      ourEphemeralPubKey,
      previousCounter,
      counter,
      buffer
    ]);
  }

  async function SignalCoreDecrypt(
    ourIdentityPubKey,
    theirIdentityPubKey,
    remoteEphemeralKey,
    messageKey,
    previousCounter,
    counter,
    ciphertext,
    tag8,
  ) {
    await checkIfInitialized();
    return callWithProto(FStarDecrypt(ciphertext.byteLength + 57), [
      ourIdentityPubKey,
      theirIdentityPubKey,
      remoteEphemeralKey,
      messageKey,
      previousCounter,
      counter,
      ciphertext,
      tag8
    ]);
  }

  async function SignalCoreAESEnc(key, iv, data) {
    await checkIfInitialized();
    return callWithProto(FStarAESEnc(data.byteLength + 16), [
      key,
      iv,
      data
    ])
  }

  async function SignalCoreAESDec(key, iv, data) {
    await checkIfInitialized();
    return callWithProto(FStarAESDec(data.byteLength), [
      key,
      iv,
      data
    ])
  }

  async function SignalCoreHMAC(key, data) {
    await checkIfInitialized();
    return callWithProto(FStarHMAC, [key, data]);
  }

  async function SignalCoreSHA512(data) {
    await checkIfInitialized();
    return callWithProto(FStarSHA512, [data]);
  }

  async function SignalCoreHKDF(input, salt, info) {
    await checkIfInitialized();
    let keys = callWithProto(FStarHKDF, [input, salt, info]);
    var T1 = new ArrayBuffer(32);
    var T2 = new ArrayBuffer(32);
    var T3 = new ArrayBuffer(32);
    (new Uint8Array(T1)).set(new Uint8Array(keys).slice(0, 32));
    (new Uint8Array(T2)).set(new Uint8Array(keys).slice(32, 64));
    (new Uint8Array(T3)).set(new Uint8Array(keys).slice(64, 96));
    return [T1, T2, T3];
  }

  async function SignalCoreEd25519Sign(privKey, message) {
    await checkIfInitialized();
    return callWithProto(FStarEd25519Sign, [privKey, message]);
  }

  function validatePubKey(pubKey) {
    if (pubKey === undefined || ((pubKey.byteLength != 33 || new Uint8Array(pubKey)[0] != 5) && pubKey.byteLength != 32)) {
      throw new Error("Invalid public key");
    }
    if (pubKey.byteLength == 33) {
      return pubKey.slice(1);
    } else {
      console.error("WARNING: Expected pubkey of length 33, please report the ST and client that generated the pubkey");
      return pubKey;
    }
  }

  async function SignalCoreECDHE(pubKey, privKey) {
    await checkIfInitialized();
    let correctPubKey = validatePubKey(pubKey);
    return callWithProto(FStarECDHE, [privKey, correctPubKey]);
  }
  async function SignalCoreEd25519Verify(pubKey, msg, sig) {
    await checkIfInitialized();
    let res = callWithProto(FStarEd25519Verify, [sig, pubKey, msg]);
    if (res !== true) {
      throw new Error("Invalid signature");
    }
  }

  return {
    checkIfInitialized: checkIfInitialized,
    SignalCoreVerifySig: SignalCoreVerifySig,
    SignalCoreSign: SignalCoreSign,
    SignalCoreGenerateRegistrationId: SignalCoreGenerateRegistrationId,
    SignalCoreCreateKeyPair: SignalCoreCreateKeyPair,
    SignalCoreRatchet: SignalCoreRatchet,
    SignalCoreInitiate: SignalCoreInitiate,
    SignalCoreRespond: SignalCoreRespond,
    SignalCoreFillMessagesKeys: SignalCoreFillMessagesKeys,
    SignalCoreEncrypt: SignalCoreEncrypt,
    SignalCoreDecrypt: SignalCoreDecrypt,
    SignalCoreAESEnc: SignalCoreAESEnc,
    SignalCoreAESDec: SignalCoreAESDec,
    SignalCoreHMAC: SignalCoreHMAC,
    SignalCoreSHA512: SignalCoreSHA512,
    SignalCoreHKDF: SignalCoreHKDF,
    SignalCoreEd25519Sign: SignalCoreEd25519Sign,
    SignalCoreECDHE: SignalCoreECDHE,
    SignalCoreEd25519Verify: SignalCoreEd25519Verify,
  }
})();
