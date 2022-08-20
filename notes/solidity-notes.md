1. A simplification on the semantics of op_send, refering to its definition.
  In solidity, the execution is deterministic if the initial stack height and gas supply is given.
  However, counting stack height and gas consumption cause the verfication cumbersome,
    especially when the gas consumption and stack usage themselves are not a property to be verified.
  To simplify, we model external call nondeterministically, forcing programs consider potential failures for every external call.
