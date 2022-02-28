import json

template_uint8_list = """// generated: "{content}"
let test{i}_{name} = List.Tot.map u8_from_UInt8 [
{formatted_content}
]
"""

template = """// generated: "{content}"
inline_for_extraction
let size_test{i}_{name}: size_nat = {size}
let test{i}_{name}_list : l:list uint8{{List.Tot.length l == size_test{i}_{name}}} =
  [@inline_let]
  let l = [
{formatted_content}
  ] in
  assert_norm(List.Tot.length l == size_test{i}_{name});
  l
let test{i}_{name} : lbytes size_test{i}_{name} = createL test{i}_{name}_list
"""

byte_template = "u8 0x{byte};"

bytes_per_line = 5
bytes_line_prefix = "    "
bytes_separator = " "
bytes_line_suffix = "\n"

test_base_template = """
let test{i} () =
  let res = test_setupBase test{i}_ciphersuite test{i}_skEm test{i}_pkEm test{i}_skRm test{i}_pkRm test{i}_info test{i}_enc test{i}_zz test{i}_key_schedule_context test{i}_secret test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption0_nonce test{i}_encryption1_nonce in
"""

test_psk_template = """
let test{i} () =
  let res = test_setupPSK test{i}_ciphersuite test{i}_skEm test{i}_pkEm test{i}_skRm test{i}_pkRm test{i}_info test{i}_enc test{i}_zz test{i}_key_schedule_context test{i}_secret test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption0_nonce test{i}_encryption1_nonce in
"""

test_enc_template = """
  let seq0:HPKE.seq_aead_s test{i}_ciphersuite = 0 in
  let enc_res0 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption0_aad test{i}_encryption0_plaintext seq0 test{i}_encryption0_ciphertext test{i}_encryption0_nonce in

  assert_norm (1 < pow2 (8 * 12));
  let seq1:HPKE.seq_aead_s test{i}_ciphersuite = (seq0 + 1) in
  let enc_res1 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption1_aad test{i}_encryption1_plaintext seq1 test{i}_encryption1_ciphertext test{i}_encryption1_nonce in

  assert_norm (2 < pow2 (8 * 12));
  let seq2:HPKE.seq_aead_s test{i}_ciphersuite = (seq1 + 1) in
  let enc_res2 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption2_aad test{i}_encryption2_plaintext 2 test{i}_encryption2_ciphertext test{i}_encryption2_nonce in

  assert_norm (3 < pow2 (8 * 12));
  let seq3:HPKE.seq_aead_s test{i}_ciphersuite = (seq2 + 1) in
  let enc_res3 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption3_aad test{i}_encryption3_plaintext 3 test{i}_encryption3_ciphertext test{i}_encryption3_nonce in

  assert_norm (4 < pow2 (8 * 12));
  let seq4:HPKE.seq_aead_s test{i}_ciphersuite = (seq3 + 1) in
  let enc_res4 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption4_aad test{i}_encryption4_plaintext 4 test{i}_encryption4_ciphertext test{i}_encryption4_nonce in

  assert_norm (5 < pow2 (8 * 12));
  let seq5:HPKE.seq_aead_s test{i}_ciphersuite = (seq4 + 1) in
  let enc_res5 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption5_aad test{i}_encryption5_plaintext 5 test{i}_encryption5_ciphertext test{i}_encryption5_nonce in

  assert_norm (6 < pow2 (8 * 12));
  let seq6:HPKE.seq_aead_s test{i}_ciphersuite = (seq5 + 1) in
  let enc_res6 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption6_aad test{i}_encryption6_plaintext 6 test{i}_encryption6_ciphertext test{i}_encryption6_nonce in

  assert_norm (7 < pow2 (8 * 12));
  let seq7:HPKE.seq_aead_s test{i}_ciphersuite = (seq6 + 1) in
  let enc_res7 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption7_aad test{i}_encryption7_plaintext 7 test{i}_encryption7_ciphertext test{i}_encryption7_nonce in

  assert_norm (8 < pow2 (8 * 12));
  let seq8:HPKE.seq_aead_s test{i}_ciphersuite = (seq7 + 1) in
  let enc_res8 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption8_aad test{i}_encryption8_plaintext 8 test{i}_encryption8_ciphertext test{i}_encryption8_nonce in

  assert_norm (9 < pow2 (8 * 12));
  let seq9:HPKE.seq_aead_s test{i}_ciphersuite = (seq8 + 1) in
  let enc_res9 = test_encryption test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_encryption9_aad test{i}_encryption9_plaintext 9 test{i}_encryption9_ciphertext test{i}_encryption9_nonce in
"""

test_exp_template = """
let exp_res0 = test_export test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_export0_exportContext test{i}_export0_len test{i}_export0_exportValue in

  let exp_res1 = test_export test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_export1_exportContext test{i}_export1_len test{i}_export1_exportValue in

  let exp_res2 = test_export test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_export2_exportContext test{i}_export2_len test{i}_export2_exportValue in

  let exp_res3 = test_export test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_export3_exportContext test{i}_export3_len test{i}_export3_exportValue in

  let exp_res4 = test_export test{i}_ciphersuite test{i}_key test{i}_nonce test{i}_exporterSecret test{i}_export4_exportContext test{i}_export4_len test{i}_export4_exportValue in

  enc_res0 && enc_res1 && enc_res2 && enc_res3 && enc_res4 && enc_res5 && enc_res6 && enc_res7 && enc_res8 && enc_res9 && res && exp_res0 && exp_res1 && exp_res2 && exp_res3 && exp_res4
"""




def string_to_formatted_byte_list(string):
    bytes = []
    formatted = ""

    # construct single bytes
    for i in range(0, len(string), 2):
        byte = string[i:i+2]
        bytes.append(byte_template.format(**locals()))

    # format bytes in lines of some bytes per line
    num_bytes = len(bytes)
    for i, byte in enumerate(bytes):
        if i % bytes_per_line == 0:
            formatted += bytes_line_prefix
        formatted += byte
        if i < num_bytes - 1:
            if i % bytes_per_line == bytes_per_line - 1:
                formatted += bytes_line_suffix
            else:
                formatted += bytes_separator

    return num_bytes, formatted


def format_variable(i, name, content):
    size, formatted_content = string_to_formatted_byte_list(content)
    return template.format(**locals())

modes = ['Base', 'PSK', 'Auth', 'AuthPSK']

def format_mode(i, content):
    mode = modes[content]
    return f"let test{i}_mode: HPKE.mode = HPKE.{mode}"

kems = {16: "DH.DH_P256, Hash.SHA2_256", 32: "DH.DH_Curve25519, Hash.SHA2_256"}
kdfs = {1: "Hash.SHA2_256", 2: "Hash.SHA2_384", 3: "Hash.SHA2_512"}
aeads = {1: "AEAD.AES128_GCM", 2: "AEAD.AES256_GCM", 3: "AEAD.CHACHA20_POLY1305"}

def format_ciphersuite(i, kem, kdf, aead):
    the_kem = kems[kem]
    the_kdf = kdfs[kdf]
    the_aead = aeads[aead]
    return f"let test{i}_ciphersuite: HPKE.ciphersuite = {the_kem}, {the_aead}, {the_kdf}"

def format_len(i, key, content):
    return f"let test{i}_{key}:size_nat = {content}"

def format_case(i, case):
    out = ""

    try:
        if not case["mode"] == 0:
            # We only support the Base mode at the moment
            raise KeyError

        out += format_mode(i, case["mode"]) + "\n"
        out += format_ciphersuite(i, case["kem_id"], case["kdf_id"], case["aead_id"]) + "\n\n"

        for key, value in case.items():
            if type(value) == str:
                out += format_variable (i, key, value) + "\n"

        for j, encryption in enumerate(case["encryptions"]):
            for key, value in encryption.items():
                out += format_variable (i, f"encryption{j}_{key}", value) + "\n"

        for j, export in enumerate(case["exports"]):
            for key, value in export.items():
                if type(value) == str:
                    out += format_variable (i, f"export{j}_{key}", value) + "\n"
            out += format_len(i, f"export{j}_len", export["L"]) + "\n"

        out += test_base_template.format(**locals())
        print(out)
    except KeyError:
        print(f"// Skipped unsupported test case {i}")


with open('test-vectors.json', 'r') as tv_file:
    data = tv_file.read()

vectors = json.loads(data)

#print(vectors[0]["mode"])
#format_case(0, vectors[0])

for i, case in enumerate(vectors):
   format_case(i, case)
   print()

