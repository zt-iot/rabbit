# Simplified Camserver

Simplified camserver

- File accesses are dropped.
- Initial RPC handshake is removed.
- Loops are kept.
- Attacks are kept.


## Result of `--prove=Reachable`

- Original: processing time: 1331.51s [log.txt](log.txt)
- New: processing time: 692.98s [log.txt](log.2.txt)

```
% tamarin-prover _202_camserver.spthy --prove=Reachable | tail -30 

==============================================================================
summary of summaries:

analyzed: _202_camserver.spthy

  processing time: 1331.51s
  
  WARNING: 3 wellformedness check failed!
           The analysis results might be wrong!
  
  AlwaysStarts_ (all-traces): analysis incomplete (1 steps)
  AlwaysStartsWhenEnds_ (all-traces): analysis incomplete (1 steps)
  TransitionOnce_ (all-traces): analysis incomplete (1 steps)
  Reachable (exists-trace): verified (22 steps)

==============================================================================
```

```
% tamarin-prover _202_camserver.spthy.2 --prove=Reachable | tail -30 

==============================================================================
summary of summaries:

analyzed: _202_camserver.spthy.2

  processing time: 692.98s
  
  WARNING: 1 wellformedness check failed!
           The analysis results might be wrong!
  
  AlwaysStarts (all-traces): analysis incomplete (1 steps)
  AlwaysStartsWhenEnds (all-traces): analysis incomplete (1 steps)
  TransitionOnce (all-traces): analysis incomplete (1 steps)
  Reachable (exists-trace): verified (22 steps)

==============================================================================
```
