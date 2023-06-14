from pyteal import *

handle_creation = Seq(App.globalPut(Bytes("Count"), Int(0)), Approve())

sell_shirt_from_external = Seq(
    If(App.globalGet(Bytes("Count")) > Int(0))
    .Then(App.globalPut(Bytes("Count"), App.globalGet(Bytes("Count")) - Int(1)))
    )

router = Router(
    "Shirts",
    BareCallActions(
        no_op=OnCompleteAction.always(sell_shirt_from_external),
        opt_in=OnCompleteAction.create_only(handle_creation)
    ),
)


@router.method
def add(quantity: abi.Uint64):
    scratchCount = ScratchVar(TealType.uint64)
    return Seq(
        scratchCount.store(App.globalGet(Bytes("Count"))),
        App.globalPut(Bytes("Count"), scratchCount.load() + quantity.get()),
    )

@router.method
def sell(quantity: abi.Uint64):
    scratchCount = ScratchVar(TealType.uint64)
    return Seq(
        # InnerTxnBuilder.Begin(),
        # InnerTxnBuilder.SetFields({
        #     TxnField.type_enum: TxnType.ApplicationCall,
        #     TxnField.application_id: app_id.get(),
        #     TxnField.on_completion: OnComplete.NoOp,
        #     TxnField.application_args: [Bytes("sell")],
        # }),
        # InnerTxnBuilder.Submit(),
        # InnerTxnBuilder.Begin(),
        # InnerTxnBuilder.SetFields(
        #     {
        #         TxnField.type_enum: TxnType.ApplicationCall,
        #         TxnField.application_id: Int(1234),
        #         TxnField.on_completion: OnComplete.NoOp,
        #     }
        # ),
        #InnerTxnBuilder.Submit(),
        # InnerTxnBuilder.Begin(),
        # InnerTxnBuilder.SetFields(
        #     {
        #         TxnField.type_enum: TxnType.ApplicationCall,
        #         TxnField.application_id: app_to_call.application_id(),
        #         TxnField.on_completion: OnComplete.OptIn
        #     }
        # ),
        # InnerTxnBuilder.Submit(),
        scratchCount.store(App.globalGet(Bytes("Count"))),
        App.globalPut(Bytes("Count"), scratchCount.load() - quantity.get()),
    )


@router.method
def read_count(*, output: abi.Uint64):
    return output.set(App.globalGet(Bytes("Count")))


if __name__ == "__main__":
    import os
    import json

    path = os.path.dirname(os.path.abspath(__file__))
    approval, clear, contract = router.compile_program(version=8)

    # Dump out the contract as json that can be read in by any of the SDKs
    with open(os.path.join(path, "artifacts2/contract.json"), "w") as f:
        f.write(json.dumps(contract.dictify(), indent=2))

    # Write out the approval and clear programs
    with open(os.path.join(path, "artifacts2/approval.teal"), "w") as f:
        f.write(approval)

    with open(os.path.join(path, "artifacts2/clear.teal"), "w") as f:
        f.write(clear)