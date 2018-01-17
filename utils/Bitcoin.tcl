#!/usr/bin/env tclsh

# levels:
#   1 trivially redeemable
#   2 hashing, no signature
#   3 impossibru!
#   4 EC-signatures & "P2SH"
set ::patterns {
   {^OP_DUP OP_HASH160 '[0-9a-f]{40}' OP_EQUALVERIFY OP_CHECKSIG$} "Adr" 4
   {^OP_DUP OP_HASH160 '[0-9a-f]{40}' OP_EQUALVERIFY OP_CHECKSIG OP_NOP$} "Adr*" 4
   {^'[0-9a-f]+' OP_DROP OP_DUP OP_HASH160 '[0-9a-f]{40}' OP_EQUALVERIFY OP_CHECKSIG$} "*Adr" 4
   {^OP_[A-Z0-9]+( '[0-9a-f]+')+ OP_[A-Z0-9]+ OP_CHECKMULTISIG$} "MSig" 4
   {^'04[0-9a-f]{128}' OP_CHECKSIG$} "U-pk"  4
   {^'0[23][0-9a-f]{64}' OP_CHECKSIG$} "C-pk" 4
   {^OP_HASH160 '[0-9a-f]{40}' OP_EQUAL$} "P2SH" 4

   {^OP_DUP OP_HASH160 '[0-9a-f]{40}' OP_EQUALVERIFY OP_NOP1$} "H160Eq*" 2
   {^OP_HASH256 '[0-9a-f]{64}' OP_EQUAL$} "H256Eq" 2
   {^'[0-9a-f]+' OP_DROP OP_SHA256 '[0-9a-f]{64}' OP_EQUAL$} "*S256Eq" 2

   {^'[0-9a-f]+' OP_CHECKSIG$} "X-pk" 3
   {^OP_DUP OP_HASH160 OP_FALSE OP_EQUALVERIFY OP_CHECKSIG$} "H160Eq0" 3
   {^OP_IFDUP OP_IF OP_2SWAP OP_VERIFY OP_2OVER OP_DEPTH$} "WTF#1" 3
   {^OP_DUP OP_HASH160 '[0-9a-f]+' OP_EQUALVERIFY OP_CHECKSIG( OP_CHECKSIG)+$} "CheckSig^n" 3
   {^OP_RETURN$} "Ret" 3
   {^OP_RETURN .*$} "Ret*" 3

   {^'[0-9a-f]+' OP_NOP2 OP_DROP$} "*ε" 1
   {^OP_DUP OP_DUP OP_DUP$} "Du³" 1
   {^OP_3 OP_DROP OP_DROP OP_TRUE$} "*DrT" 1
   {^'[0-9a-f]+'$} "val" 1
   {^OP_MIN OP_3 OP_EQUAL$} "M3Eq" 1
   {^'[0-9a-f]+' OP_DROP '[0-9a-f]+' OP_DROP OP_TRUE$} "**True" 1
   {^'[0-9a-f]+' OP_DROP OP_TRUE$} "*True" 1
   {^OP_TRUE$} "True" 1
   {^$} "ε" 1
}

proc vars args { foreach var $args { uplevel 1 [list variable $var] } }
catch {rename puts _puts}
proc puts args { if {[catch { _puts {*}$args }]} then { exit } }

namespace eval Secp256k1 {
    # The prime:
    variable P [expr {2**256 - 2**32 - 0xF * 2**6 - 2**4 - 1}]
    # parameters of elliptic curve:
    variable A 0 B 7 ;      # that is: y² = x³ + 7
    # generating point G:
    variable Gc "02 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798"
    variable Gu "04 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798 483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8"
    variable G ""; # coords of generating point are obtained later

    # order n and cofactor h of G on elliptic curve:
    variable N "" H 1 
    scan FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 %llx N

    # field-ops:
    proc neg {x}      { variable P; expr { $x ? ($P-$x) : $x } }
    proc inv {x}      { variable P; expr {[exteuc $P $x] % $P } }
    proc add {x y}    { variable P; expr {($x + $y) % $P} }
    proc add3 {x y z} { variable P; expr {($x + $y +$z) % $P} }
    proc sub {x y}    { variable P; expr {($x - $y) % $P} }
    proc sub3 {x y z} { variable P; expr {($x - $y -$z) % $P} }
    proc mul {x y}    { variable P; expr {($x * $y) % $P} }
    proc mul3 {x y z} { variable P; expr {($x * $y * $z) % $P} }
    proc div {x y}    { mul $x [inv $y] }
    proc pow {x n}    { repeat + 1 inv mul $x $n }
    proc sqrt {x}     { variable P; pow $x [expr {($P+1)/4}] }

    # extended euclidean algorithm: reference impl
    #proc exteuc-recursive {a b} {
    #    if {$b == 1} { return [list 0 $b] }; set q [expr {$a / $b}]
    #    lassign [exteuc-recursive $b [expr {$a - $q * $b}]] s1 t1
    #    return [list $t1 [expr {$s1 - $t1 * $q}]]
    #}
    #proc exteuc {a b} { lindex [exteuc-recursive $a $b] 1 }

    # extended euclidean algorithm: needed for inv & div 
    proc exteuc-iterative {a b} {
        set s 1; set t 0
        while {$b != 1} {
            set q [expr {$a / $b}]
            set b [expr {$a - $q * [set a $b]}]
            set s [expr {$t - $q * [set t $s]}]
        }; return $s
    }
    proc exteuc {a b} { exteuc-iterative $a $b }

    # calculate ($base ^ $exp) for the specified calculus.
    proc repeat {v zero inv op base exp} {
        if {$exp == 0} { return $zero }
        if {$exp > 0} { "repeat_aux$v" $zero $inv $op $base $exp
        } else { $inv [ "repeat_aux$v" $zero $inv $op $base [expr {-$exp}]] }
    }
    # simple variant that does not use "inv"
    proc repeat_aux+ {zero inv op base exp} {
        set res $zero; set pob $base; # pob is power of base
        while {$exp > 0} {
            if {$exp & 1} { set res [$op $res $pob] }
            set exp [expr {$exp / 2}]; set pob [$op $pob $pob]
        }
        return $res
    }
    # sophisticated variant that does use "inv": use only if "inv" is fast
    proc repeat_aux- {zero inv op base exp} {
        set lbit 0; set res $zero; set pob $base; # "pob" is power of base
        while {$exp > 0} {
            if {$lbit} {; # series of 1s so far.
                if {($exp & 3) == 0} {; # end of 1-streak
                    set res [$op $res [$op $pob [$inv $sb]]]
                    set lbit 0; set exp [expr {$exp / 4}]
                    set pob [$op $pob $pob]; set pob [$op $pob $pob]
                } else {; # streak goes on, maybe despite a single "0"
                    if {!($exp & 1)} { set sb [$op $sb $pob] }
                    set exp [expr {$exp / 2}]; set pob [$op $pob $pob]
                }
            } else {; # previous bit was zero
                if {($exp & 3) == 3} {; # start of new 1-streak:
                    set sb $pob; set lbit 1; set exp [expr {$exp / 4}]
                    set pob [$op $pob $pob]; set pob [$op $pob $pob]
                } else {;# no streak, maybe despite a single "1"
                    if {$exp & 1} { set res [$op $res $pob] }
                    set exp [expr {$exp / 2}]; set pob [$op $pob $pob]
                }
            }
        }
        if {$lbit} { set res [$op $res [$op $pob [$inv $sb]]] }
        return $res
    }

    # determine Y coord of point on elliptic curve given X and lastbit-of-Y
    proc getY {X sY} {
        vars A B; set Y [sqrt [add3 [mul3 $X $X $X] [mul $A $X] $B]]
        return [expr {($Y&1)!=($sY&1) ? [neg $Y] : $Y }]
    }

    # hex<->coords conversions:
    proc hex2pnt {hex} {
        scan $hex {%2x %[0-9A-F ]} type data; if {$type == 0} { return "" }
        regsub -all { } $data "" data
        switch -exact -- $type {
           4     { scan $data %64llx%64llx X Y; return [list $X $Y] }
           2 - 3 { scan $data %64llx X; return [list $X [getY $X $type]] }
           default { error "bad format" }
        }
    }
    proc pnt2hex {pnt {type 4}} {
        if {[llength $pnt]<2} { return "00" }; lassign $pnt X Y
        switch -exact -- $type {
           4     { return [format "04 %064llX %064llX" $X $Y] }
           2 - 3 { return [format "%02X %064llX" [expr {2 + ($Y&1)}] $X] }
           default { error "bad format" }
        }
    }

    # calculate internal rep (coords) for G
    set G [hex2pnt $Gu] 
    # must be same for compressed and uncompressed data:
    if {$G ne [hex2pnt $Gc]} { error "inconsistency!" }

    # EC group-operations:
    proc NEG {p} {
        if {[llength $p]<2} { return $p }
        lassign $p X Y; list $X [neg $Y]
    }
    proc ADD {p q} {
        # if any operand is O-element, return the other:
        if {[llength $p]<2} { return $q }; if {[llength $q]<2} { return $p }
        variable A; lassign $p xP yP; lassign $q xQ yQ
        if {$xP == $xQ} { # same X
            if {($yP & 1) == ($yQ & 1)} {; # same point
                set s [div [add [mul3 3 $xP $xP] $A] [mul 2 $yP]]
                set xR [sub3 [mul $s $s] $xP $xP]
                set yR [sub [mul $s [sub $xP $xR]] $yP]
            } else {; # inverse points: sum is O
                return ""
            }
        } else { # different X
            set s [div [sub $yP $yQ] [sub $xP $xQ]]
            set xR [sub3 [mul $s $s] $xP $xQ]
            set yR [sub [mul $s [sub $xP $xR]] $yP]
        }
        return [list $xR $yR]
    }
    proc MUL {p n} { return [repeat - [list] NEG ADD $p $n] }

    proc priv2pub {n} { variable G; MUL $G $n }

    # z = sha256(message) as a number (e.g. 0x<sha256>)
    # k = random number in [1, n-1]
    # d = numeric private key for signing (<0 for compressed)
    proc sign {z d k} {
        vars G N; set b 27; if {$d<0} { set d [expr {-$d}]; incr b 4 }
        set Gk [MUL $G $k]; if {[llength $Gk]<2} { error "bad k" }
        lassign $Gk xk yk; set r [expr { $xk % $N}]; if {$r==0} { error "bad k" }
        set s [expr {[exteuc $N $k] * ($z + $r * $d) % $N}]
        set b [expr { $b + 2*($r!=$xk) + ($yk&1)}]; list $b $r $s
    }
    proc getK {z r s d} {
        vars N; if {$d<0} { set d [expr {-$d}] }
        expr {(($z + $r * $d) * [exteuc $N $s]) % $N}
    }
    proc verify {z r s Gd} {
        vars G N; if {$r<1 || $s<1 || $r>=$N || $s>=$N} { error "bad sig: error" }
        set w [exteuc $N $s];set u1 [expr {$z*$w%$N}];set u2 [expr {$r*$w%$N}]
        set p [ADD [MUL $G $u1] [MUL $Gd $u2]]
        if {[llength $p]<2} { error "bad sig: O" }
        if {[lindex $p 0] % $N != $r} { error "bad sig: mismatch" }
    }
    proc check_ec {p} {
        vars A B; if {[llength $p] < 2} { return 0 }; lassign $p x y
        set lhs [mul $y $y]; set rhs [add3 [mul3 $x $x $x] [mul $A $x] $B]
        expr {$lhs == $rhs}
    }
    proc sig2pnt {z b r s} {
        vars N P G
        if {$b >= 27} { incr b -27 }; if {$b<0 || $b>=8} { error "bad sig flag" }
        set x $r; if {$b & 2} { incr x $N }; if {$x>$P} { error "x too large" }
        set Gk [list $x [getY $x $b]]; if {![check_ec $Gk]} { error "Gk not on curve" }
        if {[MUL $Gk $N] ne ""} { error "Gk**N is not O" }
        set w [exteuc $N $r];set u1 [expr {$s*$w%$N}];set u2 [expr {(-$z*$w)%$N}]
        set p [ADD [MUL $Gk $u1] [MUL $G $u2]]; return $p
    }
}

namespace eval BitcoinStruct {
    package require sha256
    variable opentxs {}

    proc getVarInt {data _pos _res} {
        upvar 1 $_pos pos $_res res
        binary scan $data "@$pos cu" b; incr pos
        if {$b == 0xff}       { binary scan $data "@$pos wu" res; incr pos 8
        } elseif {$b == 0xfe} { binary scan $data "@$pos iu" res; incr pos 4
        } elseif {$b == 0xfd} { binary scan $data "@$pos su" res; incr pos 2
        } else                { set res $b }
    }
    proc putVarInt {num} {
        if {$num < 0 || $num >= 2**64} { error "number out of bounds" }
        if {$num >= 2**32} { return [binary format "cu wu" 0xff $num] }
        if {$num >= 2**16} { return [binary format "cu iu" 0xfe $num] }
        if {$num >= 0xFD} { return [binary format "cu su" 0xfd $num] }
        return [binary format "cu" $num]
    }
    proc getTxIn {data _pos} { upvar 1 $_pos pos
        binary scan $data "@$pos a32 iu" outHash outIdx
        incr pos 36; getVarInt $data pos scriptLen
        binary scan $data "@$pos a$scriptLen iu" script seq
        incr pos $scriptLen; incr pos 4
        # hash, script: binary strings!
        return [list $outHash $outIdx $script $seq]
    }
    proc fmtTxIn {tx} { lassign $tx hash idx script seq
        binary scan [string reverse $hash] "H64" txOutHash
        if {[string trim $txOutHash "0"] eq ""} { # coinbase
            set txOutHash "<none>"; binary scan $script "H*" script
            if {$idx == 0xFFFFFFFF} { set idx "-" }
        } else { set script [BitcoinScript::disasm $script] }
        return [list $txOutHash $idx $script $seq]
    }
    proc getTxOut {data _pos} { upvar 1 $_pos pos
        binary scan $data "@$pos wu" value
        incr pos 8; getVarInt $data pos scriptLen
        binary scan $data "@$pos a$scriptLen" script
        incr pos $scriptLen; return [list $value $script]
    }
    proc getTx {data _pos limit} { upvar 1 $_pos pos; variable opentxs
        set opos $pos; binary scan $data "@$pos iu" version ; incr pos 4
        set tx [dict create version $version]

        getVarInt $data pos nInputs; set inputs ""
        for { set i 0 } { $i < $nInputs } { incr i } {
            lassign [ getTxIn $data pos ] hash idx script seq
            set key [format "%s:%d" $hash $idx]
            if {[dict exists $opentxs $key]} {
                set script [BitcoinScript::disasm $script]
                puts "used: [dict get $opentxs $key] with {$script}"
                dict unset opentxs $key
            } else { # output wasn't interesting }
        }

        getVarInt $data pos nOutputs; set outputs ""
        for { set i 0 } { $i < $nOutputs } { incr i } {
            lappend outputs [getTxOut $data pos]
        }

        binary scan $data "@$pos i" lockTime ; incr pos 4

        set txbin [string range $data $opos $pos-1]; set hash ""; set txhash ""

        set i -1
        foreach output $outputs {
            lassign $output value script; set found 0; set ftyp "unk"
            set script [BitcoinScript::disasm $script]; incr i
            #if {$value != 0} {
                foreach {re typ level} $::patterns {
                    if {[regexp $re $script]} {
                        set found $level; set ftyp $typ; break
                    }
                }
            #} else { set found 2; set ftyp "0val"; # 0-value not interesting }
            if {$found < $limit} {
                if {$hash eq ""} {
                    set hash [sha2::sha256 -bin [sha2::sha256 -bin $txbin]]
                    binary scan [string reverse $hash] "H64" txhash
                }
                set key [format %s:%d $hash $i]
                set val [list $found ($ftyp) ${txhash}:$i [expr {$value/1e8}] $script]
                dict set opentxs $key $val; puts "new: $val"
            }
            incr ::counter($ftyp); incr ::value($ftyp) $value
        }

        dict set tx locktime $lockTime

        return $tx
    }

    proc parseTx {args} {
        set data [lindex $args 0]
        if {[string is xdigit $data]} {
            set data [binary format H* $data]
        }
        binary scan $data "iu" version ; set pos 4
        set hash [sha2::sha256 -bin [sha2::sha256 -bin $data]]
        binary scan [string reverse $hash] "H64" txhash
        puts "Version: $version - Hash: $txhash"

        getVarInt $data pos nInputs; puts "Inputs: ($nInputs)"
        for { set i 0 } { $i < $nInputs } { incr i } {
            lassign [fmtTxIn [ getTxIn $data pos ]] txOutHash txOutIdx script seq
            puts "   $txOutHash:$txOutIdx {$script} $seq"
        }

        getVarInt $data pos nOutputs; puts "Outputs: ($nOutputs)"
        for { set i 0 } { $i < $nOutputs } { incr i } {
            lassign [getTxOut $data pos] value script
            set script [BitcoinScript::disasm $script]
            puts "   [format %.8f [expr {$value/1e8}]] {$script}"
        }

        binary scan $data "@$pos i" lockTime 
        puts "LockTime: $lockTime"
    }
    proc asm2bin {script} {
        if {[set hex ""; llength $script] == 1 &&
            [catch {Bitcoin::wf2hex $script} hex] == 0 &&
            [string length [lindex $hex 1]] == 40
        } then { lassign $hex code key; # looks like a bitcoin address
            switch -exact -- $code {
               00 { set script "76a914${key}88ac" }
               05 { set script "a914${key}87" }
               default { error "Unknown type of address: [lindex $hex 0]" }
            }
        } else {; # if not an address, then it must be a script.
            set script [BitcoinScript::asm $script]
        }
        set script [binary format H* $script]
        return "[putVarInt [string length $script]]$script"
    }
    proc createTx {args} {
        if {[llength $args] > 0} { set lines [join $args \n] } { set lines [read stdin] }
        set lines [split $lines \n]; set version 1; set tx ""
        set cnr 0; set cln [lindex $lines $cnr]

        if {[lindex $cln 0] eq "Version:"} {
            set version [lindex $cln 1]
            incr cnr; set cln [lindex $lines $cnr]
        }; append tx [binary format "iu" $version]

        if {[lindex $cln 0] ne "Inputs:"} { error "Invalid Syntax: expected \"Inputs:\"" }

        for {set txIn "";set nIn 0} {1} { incr nIn } {
            incr cnr; set cln [lindex $lines $cnr]
            lassign $cln txout script seq; lassign [split $txout ":"] ohash onr
            if {![string is xdigit $ohash] || ![string is integer $onr]} then {break}
            if {[string length $ohash]!=64 || $onr < 0} { error "Invalid Syntax for input: $cln"}
            if {![info exists seq] || $seq eq ""} { set seq 0xffffffff }
            append txIn [string reverse [binary format "H64" $ohash]]
            append txIn [binary format "iu" $onr] [asm2bin $script] [binary format "iu" $seq]
        }; append tx [putVarInt $nIn] $txIn

        if {[lindex $cln 0] ne "Outputs:"} { error "Invalid Syntax: expected \"Outputs:\"" }
        
        for {set txOut "";set nOut 0} {1} { incr nOut } {
            incr cnr; set cln [lindex $lines $cnr]; lassign $cln value script
            if {[llength $cln] < 2 || ![string is double $value]} then { break }
            if {$value < 0.0} { error "Invalid Syntax for output: $cln" }
            append txOut [binary format "wu" [expr {wide($value*1e8+.5)}]] [asm2bin $script]
        }; append tx [putVarInt $nOut] $txOut

        if {[lindex $cln 0] eq "LockTime:"} { set locktime [lindex $cln 1]
        } else { set locktime 0 }
        append tx [binary format "i" $locktime]
        
        binary scan $tx H* htx; return $htx
    }
    proc readBlock {fd &block limit} {
        upvar 1 ${&block} block
        set block ""; set size 0; set bmagic [read $fd 4]
        if {$bmagic ne "\xF9\xBE\xB4\xD9"} { return 0 }
        set bsize [ read $fd 4]; binary scan $bsize "iu" size
        if {$bsize eq "" || $size == 0} { return -1 }
        set data [read $fd $size]; set pos 0
        if {[string length $data] < $size} { return -1 }
        set blkHdr [string range $data 0 79]
        #set hash [sha2::sha256 -bin [sha2::sha256 -bin $blkHdr]]
        #binary scan [string reverse $hash] "H64" blkHash
        binary scan $data "@$pos iu      a32      H64    iu H8   H8 " \
                                 version prevHash merkle ts bits nonce 
        binary scan [string reverse $prevHash] "H64" prevHash
        incr pos 80; getVarInt $data pos nTx
        dict set block version     $version
        #dict set block blkhash     $blkHash
        dict set block prev_block  $prevHash
        dict set block merkle_root $merkle
        dict set block timestamp   $ts
        dict set block bits        $bits
        dict set block nonce       $nonce

        for {set i 0} {$i < $nTx} {incr i} {
            dict lappend block txs [ getTx $data pos $limit ]
        }
        return 1
    }
    proc parseChain {args} {
        set files [lsort -ascii [glob -directory ~/.bitcoin/blocks "blk*.dat"]]
        if {[llength $args]%2} { puts stderr "$::argv0 -block \[-level #\] (2-5; dft:2)"; exit }
        array unset options; array set options {-level 2};# defaults
        array set options $args; variable opentxs; set bnr 0; set limit $options(-level)
        foreach fname $files {
            set fd [open $fname "rb"]
            while {[readBlock $fd block $limit] > 0} { incr bnr
                if {$bnr % 10000 == 0} {
                    set txt "[file tail $fname]: $bnr: [array get ::counter] - [dict size $opentxs]"
                    puts stderr $txt; flush stderr
                }
            }
            close $fd
        }
        dict for {output rec} $opentxs {
            puts "$rec"
        }
        parray ::counter
        parray ::value
    }
}
namespace eval BitcoinScript {
    namespace unknown badop; proc badop args { error "bad op $args" }

    array set simpleops {
        00  OP_FALSE       4f  OP_1NEGATE     51  OP_TRUE        61  OP_NOP
        63  OP_IF          64  OP_NOTIF       67  OP_ELSE        68  OP_ENDIF
        69  OP_VERIFY      6a  OP_RETURN      6b  OP_TOALTSTACK  6c  OP_FROMALTSTACK 
        6d  OP_2DROP       6e  OP_2DUP        6f  OP_3DUP        70  OP_2OVER
        71  OP_2ROT        72  OP_2SWAP       73  OP_IFDUP       74  OP_DEPTH
        75  OP_DROP        76  OP_DUP         77  OP_NIP         78  OP_OVER
        79  OP_PICK        7a  OP_ROLL        7b  OP_ROT         7c  OP_SWAP
        7d  OP_TUCK        7e xOP_CAT         7f xOP_SUBSTR      80 xOP_LEFT
        81 xOP_RIGHT       82  OP_SIZE        83 xOP_INVERT      84 xOP_AND
        85 xOP_OR          86 xOP_XOR         87  OP_EQUAL       88  OP_EQUALVERIFY
        8b  OP_1ADD        8c  OP_1SUB        8d xOP_2MUL        8e xOP_2DIV  
        8f  OP_NEGATE      90  OP_ABS         91  OP_NOT         92  OP_0NOTEQUAL  
        93  OP_ADD         94  OP_SUB         95 xOP_MUL         96 xOP_DIV  
        97 xOP_MOD         98 xOP_LSHIFT      99 xOP_RSHIFT      9a  OP_BOOLAND  
        9b  OP_BOOLOR      9c  OP_NUMEQUAL    9d  OP_NUMEQUALVERIFY
        9e  OP_NUMNOTEQUAL          9f  OP_LESSTHAN              a0  OP_GREATERTHAN
        a1  OP_LESSTHANOREQUAL      a2  OP_GREATERTHANOREQUAL
        a3  OP_MIN         a4  OP_MAX         a5  OP_WITHIN      a6  OP_RIPEMD160
        a7  OP_SHA1        a8  OP_SHA256      a9  OP_HASH160     aa  OP_HASH256
        ab  OP_CODESEPARATOR        ac  OP_CHECKSIG              ad  OP_CHECKSIGVERIFY
        ae  OP_CHECKMULTISIG        af  OP_CHECKMULTISIGVERIFY   fd  OP_PUBKEYHASH
        fe  OP_PUBKEY      ff  OP_INVALIDOPCODE
        00* OP_0           51* OP_1

        50  OP_RESERVED    62  OP_VER   65  OP_VERIF   66  OP_VERNOTIF
        89  OP_RESERVED1   8a  OP_RESERVED2 
        b0  OP_NOP1   b1  OP_NOP2   b2  OP_NOP3   b3  OP_NOP4   b4  OP_NOP5   
        b5  OP_NOP6   b6  OP_NOP7   b7  OP_NOP8   b8  OP_NOP9   b9  OP_NOP10 
        52  OP_2      53  OP_3      54  OP_4      55  OP_5      56  OP_6
        57  OP_7      58  OP_8      59  OP_9      5a  OP_10     5b  OP_11
        5c  OP_12     5d  OP_13     5e  OP_14     5f  OP_15     60  OP_16
    }; array set opsrev [lreverse [array get simpleops]]
    proc op_n {sn n} { upvar 2 $sn s; set dx ""; binary scan $s "H[expr {$n*2}] a*" dx s; return "'$dx'" }
    for {set i 1} {$i<=75} {incr i} { proc op[format %02x $i] {sn} "op_n \$sn $i" }
    proc op4c {sn} { upvar 1 $sn s; binary scan $s "cu a*" n s; op_n $sn $n } 
    proc op4d {sn} { upvar 1 $sn s; binary scan $s "su a*" n s; op_n $sn $n } 
    proc op4e {sn} { upvar 1 $sn s; binary scan $s "iu a*" n s; op_n $sn $n } 

    proc disasm {s} {
        set res ""; variable simpleops
        while {$s ne ""} {
            binary scan $s[set s ""] "H2 a*" opx s
            if {[info exists simpleops($opx)]} {
                lappend res $simpleops($opx)
            } elseif {[info proc op$opx] ne ""} {
                lappend res [op$opx s]
            } else {
                set dx ""; binary scan $s "H*" dx
                set s ""; lappend res "data:$dx"
            }
        }
        return $res
    }
    proc disasmhex {h} {
        if {[string is xdigit $h]} {
            set ret [disasm [binary format H* $h]]
        } else { set ret [disasm $h] }
        return $ret
    }
    proc asm {asm} {
        set script ""; variable opsrev
        foreach op [string map {' ""} $asm] {
            if {[string is xdigit $op]} {
                set len [string length $op]; set blen [expr {$len/2}]
                if {$len % 2} { error "odd-length operand: $op" }
                if { $blen < 256 } {
                   binary scan [binary format cu $blen] H2 xlen
                   if { $blen > 75 } { set xlen "4c$xlen" }
                } elseif { $blen < 256**2 } {
                   binary scan [binary format su $blen] H4 xlen
                   set xlen "4d$xlen"
                } elseif { $blen < 256**4 } {
                   binary scan [binary format iu $blen] H8 xlen
                   set xlen "4e$xlen"
                } else { error "hex-string too long???" }
                append script $xlen $op
            } elseif {[info exists opsrev($op)]} {
                append script [string trimright $opsrev($op) "*"]
            } else { error "unknown: $op"; }
        }
        return $script
    }
}

namespace eval Base32 {
    variable B32 qpzry9x8gf2tvdw0s3jn54khce6mua7l

    # convert a hex-string to base32
    proc hex_to_b32 {hex} { seq_to_b32 [hex_to_seq $hex] }

    proc hex_to_seq {hex} {
        set num 0; set seq {}; set src 0
        foreach x [split $hex {}] { scan $x %x x
            set num [expr {($num<<4)+$x}]; incr src 4
            if {$src>=5} {
                lappend seq [expr {($num >> ($src-5)) & 0x1f}]
                set num [expr {$num & 0x1ff}]; incr src -5
            }
        }; if {$src} { lappend seq [expr {($num<<(5-$src))&0x1f}] }
        return $seq
    }
    proc seq_to_b32 {seq} {
       variable B32; join [lmap v $seq { string index $B32 $v }] ""
    }

    # convert a base58-string to hex
    proc b32_to_hex {b32} { seq_to_hex [b32_to_seq $b32] }

    proc b32_to_seq {b32} {
       variable B32; lmap v [split $b32 {}] { string first $v $B32 }
    }
    proc seq_to_hex {seq} {
        set num 0; set hex {}; set src 0
        foreach v $seq {
            set num [expr {($num<<5)+$v}]; incr src 5
            if {$src>=8} {
                append hex [format %02x [expr {($num >> ($src-8)) & 0xff}]]
                set num [expr {$num & 0xfff}]; incr src -8
            }
        }; # if {$src} { lappend seq [expr {($num<<(5-$src))&0x1f}] }
        return $hex
    }
}

namespace eval Base58 {
    variable B58 123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz

    # convert a hex-string to base58
    proc h2b {hex} {
        variable B58; scan $hex %llx num; set res ""
        while {$num} {
            append res [string index $B58 [expr {$num%58}]]
            set num [expr {$num/58}]
        }; return [string reverse $res]
    }

    # convert a base58-string to hex
    proc b2h {b} {
        variable B58; set num 0
        foreach bc [split $b ""] {
            set dig [string first $bc $B58]
            if {$dig<0} { error fail }
            set num [expr {$num*58 + $dig }]
        }; set hex [format "%llx" $num]
        if {[string length $hex] % 2} { set hex "0$hex" }
        return $hex
    }
}

namespace eval BitCash {

    proc sizecode {hex} {
        set sizetab {40 0 48 1 56 2 64 3 80 4 96 5 112 6 128 7};# 160 - 512
        set len [string length $hex]
        if {[dict exists $sizetab $len]} {
            return [dict get $sizetab $len]
        } else { error "Invalid size." }
    }

    proc polymod {seq} {
        set c 1; set gf32 {1 0x98f2bc8e61 2 0x79b76d99e2 4 0xf33e5fb3c4 8 0xae2eabe2a8 16 0x1e4f43e470}
        foreach d $seq {
            set c0 [expr { $c >> 35 }]
            set c [expr { (($c & 0x07ffffffff) << 5) ^ $d}]
            dict for {b v} $gf32 {
               if {$c0 & $b} { set c [expr {$c ^ $v}] }
            }
            #puts "[format "%02x   %02x   %010llx"  $d $c0 $c]"
        }
        return [expr {$c ^ 1}]
    }
    proc prefix_expand {pref} {
        set seq [ lmap ch [split $pref {}] { expr {[scan $ch %c] & 0x1f} } ]
        return [ lappend seq 0 ]
    }
    proc create_checksum {pref data} {
        set seq     [ prefix_expand $pref ]
        lappend seq {*}$data
        lappend seq {*}[lrepeat 8 0]

        set polymod [ polymod $seq ]
        lmap i {35 30 25 20 15 10 5 0} { expr {($polymod >> $i) & 0x1f} }
    }
    proc pack_addr_data {code hex} {
        array set typetab {00 0 05 8}
        set vbyte [expr {[sizecode $hex] + $typetab($code)}]
        return [Base32::hex_to_seq "[format %02x $vbyte]${hex}" ]
    }

    proc encode {pref code hex} {
        set seq [pack_addr_data $code $hex]
        set checksum [create_checksum $pref $seq]
        return ${pref}:[Base32::seq_to_b32 [concat $seq $checksum]]
    }
    proc decode {addr} {
        set laddr [split $addr ":"]
        if {[llength $laddr] < 2} {
            set pref bitcoincash; set payl [lindex $laddr 0]
        } else {
            lassign $laddr pref payl
        }
        set lpref [prefix_expand $pref]; set data [Base32::b32_to_seq $payl]
        set polymod [polymod [concat $lpref $data] ]
        if {$polymod} { error "Checksum failure." }

        set hex [Base32::seq_to_hex [lrange $data 0 end-8] ]
        array set codetab {0 00 1 05}
        set xtype [string range $hex 0 1]; set rest [string range $hex 2 end]
        set dlen [sizecode $rest]; set type -1; scan $xtype %x type
        if {$type >= 0} {
            set elen [expr {$type & 0x7}]; set code $codetab([expr {$type >> 3}])
            if {$elen!=$dlen} { error "Size mismatch" }
        } else { set code "" }
        return [list $code $rest ]
    }

    proc hex2wf {code xkey} {
        encode "bitcoincash" $code $xkey
    }
    proc wf2hex {addr} {
        decode $addr
    }
}
namespace eval Bitcoin {
    package require sha256
    package require ripemd160

    # convert a hex-string to base58 Wallet-format
    #   code: two hex-digits for the prefix (e.g. 00 for btc-address)
    #   xkey: pubkey-hash or privkey as hexadecimal string.
    proc hex2wf {code xkey} {
        if {[string length $xkey] & 1} { set xkey "0$xkey" }
        set xkey "${code}${xkey}"; set bkey [binary format H* $xkey]
        set sha [sha2::sha256 [sha2::sha256 -bin $bkey]]
        set wf [Base58::h2b ${xkey}[string range ${sha} 0 7]]
        if {$code eq "00"} { set wf "1$wf" }; return $wf
    }
    # convert a public key (compressed or uncompressed) to a btc-address
    proc pub2adr {xpub} {
        set bpub [binary format H* [regsub -all { } $xpub {}]]
        hex2wf 00 [ripemd::ripemd160 -hex [sha2::sha256 -bin $bpub ] ]
    }
    # parse a priv-key from WIF (wallet import format)
    #   wf: wallet-format string (base58 with checksum)
    proc wf2hex {wf {code {}}} {
        set hex [Base58::b2h $wf]; set check [string range $hex end-7 end]
        set data [string range $hex 0 end-8]
        if {[string length $data] < 42} {
            # shorter than 20 netto bytes? probably a btc-address.
            set data [format %042s $data]
        }
        set sha [sha2::sha256 [sha2::sha256 -bin [binary format H* $data] ] ]
        set sha [string range $sha 0 7]; set head [string range $data 0 1]
        set tail [string range $data 2 end]
        if {![string equal -nocase $check $sha]} { error "checksum fail" }
        if {$code ne "" && $code ne $head} {
            error "unexpected initial byte $head"
        }
        return [list $head $tail]
    }
    # 
    proc priv2pub {n {code 4}} {
        lassign [wf2hex $n 80] typ data; puts "typ: $typ"
        hex2pub $data $code
    }
    proc brain2pub {txt {code 4}} { hex2pub [sha2::sha256 $txt] $code }

    proc int2pub   {num {code {}}} { set defltcode 4
        if {$num < 0} { set defltcode 2; set num [expr {-$num}] }
        if {$code eq ""} { set code $defltcode }
        hex2pub [format %064llx $num] $code
    }

    proc hex2pub {hex {code {}}} { set defltcode 4
        if {[string length $hex]==66 && [string match "*01" $hex]
        } then { set hex [string range $hex 0 end-2]; set defltcode 2 }
        if {$code eq ""} { set code $defltcode }
        if {$code != 4} { set app "01" } else { set app "" }
        puts "data: $hex\npriv: [hex2wf 80 $hex$app]"
        scan $hex %llx num; pnt2pub [Secp256k1::priv2pub $num] $code
    }
    proc pnt2pub {pnt {code 4}} {
        set hex [Secp256k1::pnt2hex $pnt $code]; puts "pubKey: $hex"
        set ret [pub2adr $hex]; puts "-> https://blockchain.info/address/$ret"
        return $ret
    }
    proc rand256 {} {
        set fd [open "/dev/urandom" "rb"]; set db [read $fd 32]; close $fd
        binary scan $db H64 dx; scan $dx %llx rnd; return $rnd
    }
    proc hashmsg {msg} {
        set prefix "Bitcoin Signed Message:\n"
        #scan [sha2::sha256 [sha2::sha256 -bin $prefix$msg]] "%llx" h
        scan [hash $prefix$msg] "%llx" h
        return $h
    }
    proc sign {msg priv {k {}}} {
        set z [hashmsg $msg]; if {$k eq ""} { set k [rand256] }
        while {[catch {Secp256k1::sign $z $priv $k} rs]} {set k [rand256]}
        lassign $rs b r s; format "%02x %llx %llx" $b $r $s
    }
    proc verify {msg brs} {
        scan $brs "%2x %64llx %64llx" b r s; set z [hashmsg $msg];
        puts [format "b=%x\nr=%064llx\ns=%064llx" $b $r $s]
        set Gd [Secp256k1::sig2pnt $z $b $r $s]
        puts [format "xd=%064llx\nyd=%064llx" {*}$Gd 0 0]
        Secp256k1::verify $z $r $s $Gd;# throws error on mismatch
        pnt2pub $Gd [expr {(($b-27) & 4) ? 2 : 4}]
    }
}

proc ptime {lab scr {n 1}} { puts "$lab: [uplevel 1 [list time $scr $n]]" }
proc perftest args {
   set num [lindex $args 0]; set P $Secp256k1::P; set N $Secp256k1::N
   set G $Secp256k1::G; set 2Gi [Secp256k1::ADD $G $G]

   set gc [expr {(10**100 + isqrt(5*10**200)) / 2}] ;# -> 16180339...
   set worstcase [expr {$P * 10**100 / $gc }]

   puts "empty? ->[Secp256k1::priv2pub $N]<-"

   ptime ee-wc {Secp256k1::exteuc $P $worstcase} $num

   #ptime ADDeq {Secp256k1::ADD $2Gi $2Gi} $num
   #ptime ADDne {Secp256k1::ADD $G  $2Gi} $num
   #ptime p2p {Secp256k1::priv2pub $N} $num
   #puts "\n[Secp256k1::exteuc {*}$args]"
}

set args [lrange $argv 1 end]
switch -- [lindex $argv 0] {
    -h - -help {
        puts "Options: \n\
                 -priv 5... \n\
              or -brain \"brainwallet\" \n\
              or -int 42  or -int 0xfedCBA987...\n\
              or -hex fedcba... \n\
              or -adr 1BtcAddr..."
    }
    -p - -priv  { puts [Bitcoin::priv2pub  {*}$args] }
         -pub   { puts [Bitcoin::pub2adr   {*}$args] }
    -b - -brain { puts [Bitcoin::brain2pub {*}$args] }
    -i - -int   { puts [Bitcoin::int2pub   {*}$args] }
    -a - -adr   { puts [Bitcoin::wf2hex    {*}$args] }
    -d - -disasm { puts [BitcoinScript::disasmhex {*}$args] }
         -asm   { puts [BitcoinScript::asm {*}$args] }
    -block      { puts [BitcoinStruct::parseChain {*}$args] }
    -tx         { puts [BitcoinStruct::parseTx {*}$args] }
    -ctx        { puts [BitcoinStruct::createTx {*}$args] }
    -eval { puts [namespace eval Bitcoin $args] }
    -perf { perftest {*}$args }
}
