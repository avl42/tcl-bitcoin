tcl-bitcoin
===========

Bitcoin-related stuff using the scripting language Tcl(/Tk)
<ul>

<li>gui/btcspend.tcl:
   a coin-control GUI relying on bitcoind for the heavy lifting.
      (requires the wallet to be unlocked.)

<li>util/Bitcoin.tcl:
   wild collection of bitcoin-related stuff: <ul>
     <li> Secp256k1-math
     <li> Bitcoin script disassembly &amp; assembly
     <li> dumping &amp; undumping of bitcoin transactions
     <li> creating brainwallets (compressed or uncompressed)
     <li> See the resulting Bitcoin address for priv-keys (in wf or as numbers)
     <li> analyzer for the blockchain that finds unspent nonstandard tx-outputs
  </ul>
</ul>   

Dependencies:
Both scripts require tcl and tcllib; gui also requires tk and tklib.
