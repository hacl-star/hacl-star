include "../../../obj/crypto/aes/aes.gen.dfy"
include "../../arch/x86/print.s.dfy"
include "../../lib/util/Io.s.dfy"

module AESMain {

import opened aes_vale
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

    printHeader(asm_choice);
    if asm_choice_name[..] == "MASM" {
        print(".XMM\n");
    }
    checkConstantTimeAndLeakageBeforePrintProc("KeyExpansionStdcall",
        va_code_KeyExpansionStdcall(Secret),
        0, 8,
        TaintState(map[0 := Public, 1 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public], map[1 := Public, 2 := Public, 3 := Public], Secret),
        "@8", asm_choice, platform_choice);
    checkConstantTimeAndLeakageBeforePrintProc("KeyExpansionAndInversionStdcall",
        va_code_KeyExpansionAndInversionStdcall(Secret),
        0, 12,
        TaintState(map[0 := Public, 1 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public], map[1 := Public, 2 := Public, 3 := Public], Secret),
        "@12", asm_choice, platform_choice);

    checkConstantTimeAndLeakageBeforePrintProc("AES128EncryptOneBlockStdcall",
        va_code_AES128EncryptOneBlockStdcall(),
        0, 12,
        TaintState(map[0 := Public, 1 := Public, 2 := Public], map[], map[], Secret),
        TaintState(map[], map[X86Eax := Public], map[], Secret),
        "@12", asm_choice, platform_choice);
    // The following routines aren't really meant to be exported, but until we have CBC routines to export
    // we'll export these.

    checkConstantTimeAndLeakageBeforePrintProc("AES128EncryptOneBlock",
        va_code_AES128EncryptOneBlock(Secret),
        0, 8,
        TaintState(map[], map[X86Eax := Public], map[], Secret),
        TaintState(map[], map[], map[2 := Public], Secret),
        "@8", asm_choice, platform_choice);
    checkConstantTimeAndLeakageBeforePrintProc("AES128DecryptOneBlock",
        va_code_AES128DecryptOneBlock(Secret),
        0, 8,
        TaintState(map[], map[X86Eax := Public], map[], Secret),
        TaintState(map[], map[], map[2 := Public], Secret),
        "@8", asm_choice, platform_choice);

    //  printProc("_aes_main_i_AES128EncryptOneBlock@0", code_AES128EncryptOneBlock, 0, 8);
    //  printProc("_aes_main_i_AES128DecryptOneBlock@0", code_AES128DecryptOneBlock, 0, 8);

    printFooter(asm_choice);
}

}
