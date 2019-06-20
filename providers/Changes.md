### June 20th, 2019
- EverCrypt now supports arbitrary length IV for AES-GCM. A new parameter `iv_len` needs to be passed during encryption and decryption. In C, a new error InvalidIVLength is returned if the length of the iv does not satisfy an algorithm's requirements.
