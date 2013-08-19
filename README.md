tcl-bitcoin
===========

Bitcoin-related stuff using the scripting language Tcl(/Tk)

gui/btcspend.tcl:
   A coin-control GUI relying on bitcoind for the heavy lifting.
      (requires the wallet to be unlocked.)

util/Bitcoin.tcl:
   Wild collection of bitcoin-related stuff:
     - Secp256k1-math
     - Bitcoin script disassembly & assembly
     - dumping & undumping of bitcoin transactions
     - creating brainwallets (compressed or uncompressed)
     - See the resulting Bitcoin address for priv-keys (in wf or as numbers)
     - analyzer for the blockchain that finds unspent nonstandard tx-outputs
   

Dependencies:
Both scripts require tcl and tcllib; gui also requires tk and tklib.
