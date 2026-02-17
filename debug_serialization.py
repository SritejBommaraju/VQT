import json
import numpy as np
import dataclasses
from dataclasses import dataclass
from typing import Any

# Replicate VQTEncoder logic
class VQTEncoder(json.JSONEncoder):
    def default(self, obj):
        if hasattr(obj, 'item'): 
            print(f"Encoding numpy type: {type(obj)}")
            return obj.item()
        if hasattr(obj, 'tolist'): 
            print(f"Encoding numpy array: {type(obj)}")
            return obj.tolist()
        if isinstance(obj, complex):
            print(f"Encoding complex: {type(obj)}")
            return str(obj)
        print(f"Encoding default: {type(obj)}")
        return super().default(obj)

def test():
    print("Testing Serialization...")
    
    # 1. Complex Number
    c = 1.0 + 2.0j
    try:
        json.dumps(c, cls=VQTEncoder)
        print("Complex: OK")
    except Exception as e:
        print(f"Complex: FAIL {e}")

    # 2. Numpy scalar
    f = np.float64(0.99)
    try:
        json.dumps(f, cls=VQTEncoder)
        print("Numpy Float: OK")
    except Exception as e:
        print(f"Numpy Float: FAIL {e}")

    # 3. Numpy bool
    b = np.bool_(True)
    try:
        json.dumps(b, cls=VQTEncoder)
        print("Numpy Bool: OK")
    except Exception as e:
        print(f"Numpy Bool: FAIL {e}")
        
    # 4. Dictionary with mixed types
    data = {
        "complex": c,
        "np_float": f,
        "np_bool": b,
        "list": [c, f, b]
    }
    try:
        json.dumps(data, cls=VQTEncoder)
        print("Dict: OK")
    except Exception as e:
        print(f"Dict: FAIL {e}")

if __name__ == "__main__":
    test()
