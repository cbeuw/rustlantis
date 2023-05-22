#!/usr/bin/env python3

import os
import subprocess

miri_out = """
    12937252372391245832
    12937252372391245832
    12214221673677315835
    12997614083220014842
    13006691064920443081
    18050651553109536515
    12868690851421459990
    17615299729982132934
    17904055476842343357
    8000086602724283499
    9681823719123116033
    6190162021149800896
    12775492752284493794
    3301843803685047375
    11081091891063365362
    16364814696476250506
    9180767732859405715
    7353840400516424166
    13429956356598726483
    1092777767166105847
    13344547151687980977
    15979941507089189083
    12454281848877636227
    (false,)
    hash: 12454281848877636227
"""

llvm_out = """
    6566371006373759375
    6566371006373759375
    6769256679853301958
    7150422847530332995
    6746138021069181483
    13704941788242745003
    6631596298476415448
    1902412940186887348
    3695266874058792913
    3898679208903691186
    654699849328179901
    6172445517514086036
    17310974252921888140
    12188413833430569459
    2697032911197308816
    1658317769906441609
    8021125921775436074
    18095999266532217797
    6613087222843338599
    14245860108482326028
    6040788494499966856
    11261849907245040135
    17771821765886657718
    (false,)
    hash: 17771821765886657718
"""

def check(file: os.PathLike) -> bool:
    try:
        out = subprocess.run(["target/release/difftest", str(file)], capture_output=True, timeout=3)
    except subprocess.TimeoutExpired:
        return False
    err = out.stderr.decode(encoding = 'utf-8')
    return miri_out in err and llvm_out in err and "stderr" not in err

if __name__ == "__main__":
    with open("minimised.rs", "w", encoding='utf-8') as working:
        with open("repro.rs", "r", encoding='utf-8') as orig:
            source = orig.readlines()

        progess = True
        while progess:
            progess = False
            limit = source.index("Call(_505, bb322, dump_var(_506, _506, _506, _57))\n")
            for line in reversed(range(limit)):
                if source[line].startswith("//"):
                    continue
                print(line, end='\r')
                source[line] = f"//{source[line]}"

                working.seek(0)
                working.writelines(source)
                working.flush()

                if check(working.name):
                    progress = True
                else:
                    source[line] = source[line].removeprefix("//")
            print(f"done pass")