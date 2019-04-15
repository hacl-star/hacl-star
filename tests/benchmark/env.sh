#!/bin/bash
set -e
nob_cpus() {
    echo "[+] Setting non-boot CPUs to status $1"
    for i in /sys/devices/system/cpu/*/online; do
        echo "$1" > "$i"
    done
}
noturbo() {
    echo "[+] Setting no-turbo to status $1"
    if [[ -e /sys/devices/system/cpu/intel_pstate/no_turbo ]]; then
        echo "$1" > /sys/devices/system/cpu/intel_pstate/no_turbo
    else
        local val
        [[ $1 == 0 ]] && val=0x850089
        [[ $1 == 1 ]] && val=0x4000850089
        [[ -n $val ]] || return 0
        wrmsr -a 0x1a0 $val
    fi
}
trap "nob_cpus 1; noturbo 0;" INT TERM EXIT
noturbo 1
nob_cpus 0
./$1
Collapse

./benchmark/runbenchmark

# sudo ./run curve25519_64_vale.exe
