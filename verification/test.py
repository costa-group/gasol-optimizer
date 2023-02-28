import json
import os
import sys

sys.path.append("/home/pablo/Repositorios/ethereum/gasol-optimizer")
from verification.sfs_verify import are_equals


path_sfs1 = "sfs1.json"
path_sfs2 = "sfs2.json"


def compare():
    f1 = open(path_sfs1)
    f2 = open(path_sfs2)

    json1 = json.load(f1)
    json2 = json.load(f2)

    result = are_equals(json1,json2)
    print("Comparison: "+str(result))

if __name__ == '__main__':
    compare()

    
