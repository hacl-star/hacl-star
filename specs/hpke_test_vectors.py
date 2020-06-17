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
kdfs = {1: "Hash.SHA2_256", 3: "Hash.SHA2_512"}
aeads = {1: "AEAD.AES128_GCM", 2: "AEAD.AES256_GCM", 3: "AEAD.CHACHA20_POLY1305"}

def format_ciphersuite(i, kem, kdf, aead):
    the_kem = kems[kem]
    the_kdf = kdfs[kdf]
    the_aead = aeads[aead]
    return f"let test{i}_ciphersuite = {the_kem}, {the_aead}, {the_kdf}"

def format_len(i, key, content):
    return f"let test{i}_{key}:size_nat = {content}"

def format_case(i, case):
    out = ""

    try:
        if not case["mode"] == 0:
            raise KeyError

        out += format_mode(i, case["mode"]) + "\n"
        out += format_ciphersuite(i, case["kemID"], case["kdfID"], case["aeadID"]) + "\n\n"

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
            out += format_len(i, f"export{j}_len", export["exportLength"]) + "\n"
        print(out)
    except KeyError:
        print(f"// Skipped unsupported test case {i}")


with open('test-vectors.json', 'r') as tv_file:
    data = tv_file.read()

vectors = json.loads(data)

for i, case in enumerate(vectors):
    format_case(i, case)
    print()

