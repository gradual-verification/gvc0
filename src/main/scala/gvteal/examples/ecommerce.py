from pyteal import *


router = Router(
    "E-Commerce",
    BareCallActions(
        no_op=OnCompleteAction.create_only(Approve()),
        opt_in=OnCompleteAction.always(Approve()),
    ),
)

@router.method
def buy(shirt: abi.Application, pant: abi.Application):
    return Seq(
        InnerTxnBuilder.Begin(),
        InnerTxnBuilder.SetFields(
            {
                TxnField.type_enum: TxnType.ApplicationCall,
                TxnField.application_id: shirt.application_id(),
                TxnField.on_completion: OnComplete.NoOp
            }
        ),
        InnerTxnBuilder.Submit(),
        InnerTxnBuilder.Begin(),
        InnerTxnBuilder.SetFields(
            {
                TxnField.type_enum: TxnType.ApplicationCall,
                TxnField.application_id: pant.application_id(),
                TxnField.on_completion: OnComplete.NoOp
            }
        ),
        InnerTxnBuilder.Submit(),
    )


if __name__ == "__main__":
    import os
    import json

    path = os.path.dirname(os.path.abspath(__file__))
    approval, clear, contract = router.compile_program(version=8)

    # Dump out the contract as json that can be read in by any of the SDKs
    with open(os.path.join(path, "artifacts3/contract.json"), "w") as f:
        f.write(json.dumps(contract.dictify(), indent=2))

    # Write out the approval and clear programs
    with open(os.path.join(path, "artifacts3/approval.teal"), "w") as f:
        f.write(approval)

    with open(os.path.join(path, "artifacts3/clear.teal"), "w") as f:
        f.write(clear)