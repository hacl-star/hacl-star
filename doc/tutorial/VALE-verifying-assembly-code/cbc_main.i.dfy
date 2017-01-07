include "../../../obj/crypto/aes/cbc.gen.dfy"
include "../../arch/x86/print.s.dfy"
include "../../lib/util/Io.s.dfy"

module CBCMain {

import opened CBC
import opened x86_print_s
import opened Io_s

method {:main} Main(ghost env:HostEnvironment)
    requires env != null && allocated(env) && env.Valid();
    decreases *
{
    var argc := HostConstants.NumCommandLineArgs(env);
    if argc < 3 {
        print("Expected usage: ./[executable].exe [GCC|MASM] [Win|Linux|MacOS]\n");
        return;
    }

    var asm_choice_name := HostConstants.GetCommandLineArg(1, env);
    var platform_choice_name := HostConstants.GetCommandLineArg(2, env);
    var asm_choice;
    var platform_choice;

    if platform_choice_name[..] == "Win" {
        platform_choice := Win;
    } else if platform_choice_name[..] == "Linux" {
        platform_choice := Linux;
    } else if platform_choice_name[..] == "MacOS" {
        platform_choice := MacOS;
    } else {
        print("Please choose a correct assembler option: Win or Linux or MacOS\n");
        return;
    }

    if asm_choice_name[..] == "GCC" {
        asm_choice := GCC;
    } else if asm_choice_name[..] == "MASM" {
        asm_choice := MASM;
    } else {
        print("Please choose a correct assembler option: GCC or MASM\n");
        return;
    }

    printHeader(asm_choice );
    if asm_choice_name[..] == "MASM" {
        print(".XMM\n");
    }
    checkConstantTimeAndLeakageBeforePrintProc("aes_main_i_KeyExpansionStdcall",
        va_code_KeyExpansionStdcall(Secret),
        0, 8,
        TaintState(map[0 := Public, 1 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public], map[1 := Public, 2 := Public, 3 := Public], Secret),
        "@8", asm_choice, platform_choice);
    checkConstantTimeAndLeakageBeforePrintProc("aes_main_i_KeyExpansionAndInversionStdcall",
        va_code_KeyExpansionAndInversionStdcall(Secret),
        0, 8,
        TaintState(map[0 := Public, 1 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public], map[1 := Public, 2 := Public, 3 := Public], Secret),
        "@8", asm_choice, platform_choice);
    checkConstantTimeAndLeakageBeforePrintProc("CBCEncryptStdcall",
        va_code_CBCEncryptStdcall(),
        0, 24,
        TaintState(map[0 := Public, 1 := Public, 2 := Public, 3 := Public, 4 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public, X86Ecx := Public, X86Edx := Public], map[0 := Public, 1 := Public, 1 := Public, 2 := Public, 3 := Public], Secret),
        "@24", asm_choice, platform_choice);
    printFooter(asm_choice);
}

}
