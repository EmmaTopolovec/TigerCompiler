import os
import re
import subprocess
import sys

exe = "assemcheck"

def prRed(skk): print("\033[91m{}\033[00m" .format(skk))

def prGreen(skk): print("\033[92m{}\033[00m" .format(skk))

def findEXE():
    for filename in os.listdir("."):
        if filename.startswith(exe):
            print(filename)
            return filename

def runFiles(folder, expected):
    total = 0;
    corr = 0;

    exe = findEXE()

    for filename in filter(lambda f: f.endswith(".tig"), os.listdir(folder)):
        total += 1;
        print(filename)

        incorrect = False

        # run the program
        expected_in_fn = "in/" + filename.replace(".tig", ".txt");
        expected_comp = filename.replace(".tig", "");
        input_str = None
        if os.path.isfile(expected_in_fn):
            input_str = open(expected_in_fn, "r")

        try:
            res = subprocess.run(["sml", "@SMLload=./" + exe, folder + filename], timeout = 8, capture_output = True)
        except Exception as e:
            prRed("Timeout")
            incorrect = True

        os.remove(folder + filename + ".s")

        if os.path.exists(expected_comp):
            out = None
            try:
                res = subprocess.run(["./" + expected_comp], timeout = 4, capture_output = True, stdin = input_str)
                out = res.stdout.decode('utf-8').strip()
            except:
                prRed("Timeout")
                incorrect = True

            os.remove(expected_comp)

            if out is not None:
                expected_out_fn = "out/" + filename.replace(".tig", ".txt");

                if len(sys.argv) >= 2 and sys.argv[1] == "--out":
                    with open(expected_out_fn, "w") as out_file:
                        out_file.write(out);
                else:
                    with open(expected_out_fn, "r") as out_file:
                        correct = out_file.read()
                        if correct != out:
                            print("CORRECT:")
                            print(correct)
                            print("YOUR OUTPUT:")
                            print(out)
                            incorrect = True
        else:
            prRed("Didn't compile")
            incorrect = True


        if incorrect:
            prRed("\tIncorrect");
        else:
            corr = corr + 1;
            prGreen("\tCorrect");

    return (corr, total)

subprocess.run(["ml-build", "sources.cm", "Main.compile", exe])
(c, t) = runFiles("./testcases/", 2)

print(str(c) + "/" + str(t))
