"""
#pragma version 1
//@ requires ? && true;
//@ ensures true;
int 20
int 15
+
int 55
==
return
"""

from pyteal import *

def add_compare():
    #on_initialization = Txn.application_id() == Int(1)
    #on_update = Txn.application_id() != Int(0)
    
    #requires_clause = Or(on_initialization, on_update)
    
    int_20 = Int(20)
    int_15 = Int(15)
    int_35 = Int(55)
    
    add_expr = Add(int_20, int_15)
    eq_expr = Eq(add_expr, int_35)
    
    #program = And(requires_clause, eq_expr)    
    #return program

    return eq_expr

if __name__ == "__main__":
    with open('add.teal', 'w') as f:
        compiled = compileTeal(add_compare(), mode=Mode.Application)
        f.write(compiled)