#!/usr/bin/env tclsh

package require Tk
package require json
package require sha256
package require tablelist
catch { package require tooltip }
#package require ripemd160

wm title . BTC-Spend

set this [info script]
set btcexe bitcoin-cli

set columns {
   "#" {-width 2  -align right -sortmode dictionary }
   val {-width 10 -align right -sortmode real -changesnipside 1 }
   cf  {-width 2  -align right -sortmode dictionary }
   adr {-width 35 -align left  -sortmode ascii }
   id  {-width 15 -align left  -sortmode ascii }
}

namespace eval Base58 {
   variable B58 123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz
   proc h2b {hex} {
      variable B58; scan $hex %llx num; set res ""
      while {$num} {
         append res [string index $B58 [expr {$num%58}]]
         set num [expr {$num/58}]
      }; return [string reverse $res]
   }
   proc b2h {b} { variable B58
      set bl [split $b ""]; set num 0
      foreach bc [split $b ""] {
         set dig [string first $bc $B58]
         if {$dig<0} { return "" }
         set num [expr {$num*58 + $dig }]
      }; set hex [format "%llx" $num]
      if {[string length $hex]%2} { set hex "0$hex" }
      return $hex
   }
   proc key2wf {code xkey} {
      set xkey "${code}${xkey}"; set bkey [binary format H* $xkey]
      set sha [sha2::sha256 [sha2::sha256 -bin $bkey]]
      set wf [Base58::h2b ${xkey}[string range ${sha} 0 7]]
      if {$code eq "00"} { set wf "1$wf" }; return $wf
   }
   proc checkadr {adr} {
      set hex [b2h $adr]; if {$hex eq ""} { return 0 }
      set bin [binary format H* [format %050s $hex] ]
      set data [string range $bin 0 end-4]
      set chk [string range $bin end-3 end]
      set sha [sha2::sha256 -bin [sha2::sha256 -bin $data ] ]
      set sha [string range $sha 0 3]; string equal $chk $sha
   }
}

proc get_addresses {{minconf 0} {includeempty true}} {
   set res ""
   catch {
      set json [ exec $::btcexe listreceivedbyaddress $minconf $includeempty ]
      set res [ json::json2dict $json ]
   } msg
   return $res
}

proc get_unspent {{minconf 1} {maxconf 9999999} {adr "\[\]"}} {
   global data unconf confirmed; set res ""
   array unset data "*"; set unconf 0; set confirmed 0
   catch {
      set json [ exec $::btcexe listunspent $minconf $maxconf $adr ]
      set res [ json::json2dict $json ]
   }
   foreach row $res {
      set key [dict get $row txid]:[dict get $row vout] 
      dict set row "#" ""; set data($key) $row
      set intval [expr {wide(1e8*[dict get $row amount]+.5)}]
      if {[dict get $row confirmations]} { incr confirmed $intval
      } else { incr unconf $intval }
   }
   set confirmed [format %.8f [expr {$confirmed/1e8}]]
   set unconf [format %.8f [expr {$unconf/1e8}]]
}

# just set global data. GUI will be filled anew from it
proc init_data {} {
    get_unspent 0
}

proc refresh_addrbook {} {
   global tbla accounts; set addresses [ get_addresses ]
   catch {$tbla insert 0 "";$tbla activate 0;$tbla delete 1 end;unset accounts}
   foreach row $addresses {
      set adr [dict get $row address]; set acc [dict get $row account]
      $tbla insert end [list $adr $acc]; $tbla rowconfigure end -name $adr
      if {$acc ne ""} { set accounts($acc) $adr }
   }; catch { $tbla activate 1; $tbla delete 0; $tbla see 0 }
   $tbla sortbycolumnlist [$tbla sortcolumnlist] [$tbla sortorderlist]
}
# call init_data & apply delta-updates to the GUI
proc refresh_data {} {
   global tbl; $tbl configure -state disabled; update idletasks
   global data; array set prev [array get data]; init_data
   set chg0 ""; set chg ""; set new ""; set del ""; set cf confirmations
   foreach {key row} [array get data] {
      if {[info exists prev($key)]} {
         # "change" only if # of confirms changed from ==0 to >0
         set oldcf [dict get $prev($key) $cf]; set newcf [dict get $row $cf]
         if {($oldcf==0) ^ ($newcf==0)} { lappend chg0 $key } \
         elseif {$oldcf != $newcf} { lappend chg $key }
         unset prev($key);# remove from prev.
      } else { lappend new $key }
   }
   set del [array names prev]; array unset prev
   
   $tbl configure -state normal
   foreach key $del  { delrow $tbl $key }
   foreach key $chg0 { setrow $tbl $key $data($key) 1 }
   foreach key $chg  { setrow $tbl $key $data($key) 0 }
   foreach key $new  { addrow $tbl $key $data($key) }

   $tbl sortbycolumnlist [$tbl sortcolumnlist] [$tbl sortorderlist]
}

proc dg {k} { upvar 1 row r; dict get $r $k }
proc fmt {row} {
   set l {}; set key [dg txid]:[dg vout]
   foreach col [dict keys $::columns] {
      switch $col {
         "\#"  { lappend l [dict get $::data($key) "#"] }
         id   { lappend l $key }
         adr  { set num [dg scriptPubKey]
           if {[regexp {^76a914([0-9a-f]{40})88ac$} $num _ xpub]} {
               set num [Base58::key2wf "00" $xpub]
           }
           if {[regexp {^a914([0-9a-f]{40})87$} $num _ xpub]} {
               set num [Base58::key2wf "05" $xpub]
           }
           lappend l $num
         }
         val  {
           set num [dg amount]
           set ret [regexp -indices {\.\d+?(0+)$} $num _ p]
           if { $ret > 0 } { lassign $p f t
               set ooo [string repeat " " [expr {$t-$f+1}]]
               set num [string replace $num $f $t $ooo]
           }
           lappend l $num
         }
         cf {
           set num [dg confirmations]
           if {$num >= 100} then { set num "\u2713";# ✓ }
           lappend l $num
         }
         default { lappend l ":-)" }
      }
   }
   return $l
}

proc delrow {tbl key} {
   $tbl delete $key
}
proc addrow {tbl key row} {
   $tbl insert end [fmt $row]
   $tbl rowconfigure end -name $key
   updrow $tbl $key [dict get $row confirmations]
}
proc setrow {tbl key row from0} {
   set col [$tbl columnindex "cf"]; # only update column "cf"
   $tbl cellconfigure $key,$col -text [lindex [fmt $row] $col]
   if {$from0} { updrow $tbl $key [dict get $row confirmations] }
}
proc updrow {tbl key enabled} {
   if {$enabled} {
      $tbl rowconfigure $key -selectable 1 -fg "#000000"
      $tbl cellconfigure $key,# -text ""
   } else {
      $tbl rowconfigure $key -selectable 0 -fg "#7f7f7f"
      $tbl cellconfigure $key,# -text "\u2718"
   }
}

proc reset_click {} {
   event generate . <5>; event generate . <ButtonRelease-5>
}

proc make_gui {f} {
   catch { destroy $f }; init_data; frame $f

   make_top $f.top
   panedwindow $f.panes -orient vertical -sashrelief raised -sashwidth 5
     make_inputs $f.panes.in
     make_outputs $f.panes.out
     make_adresses $f.panes.adr
   $f.panes add $f.panes.in $f.panes.out $f.panes.adr -stretch first
   make_bottom $f.bot
   
   pack $f.top   -side top    -expand no  -fill both
   pack $f.bot   -side bottom -expand no  -fill both
   pack $f.panes -side top    -expand yes -fill both

   selection_changed
}

proc make_top {f} {
   frame $f 
   lappend entryopts -state readonly -width 12 -justify center 
   lappend entryopts -font TkHeadingFont
   label $f.l2 -text "Balance:"
   entry $f.conf -textvariable confirmed {*}$entryopts
   label $f.l1 -text "Unconf'd:"
   entry $f.unconf -textvariable unconf {*}$entryopts
   button $f.refresh -text "\u2b12↻" -command { refresh_data }
   button $f.refresh2 -text "\u2b13↻" -command { refresh_addrbook }
   button $f.reload -text "↻S" -command { source $this }
   catch { 
      tooltip::tooltip $f.refresh "Refresh Top Table Data"
      tooltip::tooltip $f.refresh2 "Refresh Bottom Table Data"
      tooltip::tooltip $f.reload  "Reload Script"
   }

   pack $f.reload -fill y -expand no -side right
   pack $f.refresh2 -fill y -expand no -side right
   pack $f.refresh -fill y -expand no -side right
   pack $f.l2 -fill y -expand no -side left
   pack $f.conf -expand yes -fill both -side left
   pack $f.l1 -fill y -expand no -side left
   pack $f.unconf -expand yes -fill both -side left
}

proc sbs {sb lo hi} {
   $sb set $lo $hi
   if {$lo <= 0.0 && $hi >= 1.0} { grid remove $sb } else { grid $sb }
}
proc make_tablelist_frame {v f cols args} {
   upvar 1 $v tbl; frame $f; set tbl $f.tbl
   scrollbar $f.vsb -orient vertical   -command [list $tbl yview] -takefocus 0
   scrollbar $f.hsb -orient horizontal -command [list $tbl xview] -takefocus 0
   tablelist::tablelist $tbl -font TkFixedFont -snipstring "\u2026" \
        -labelcommand tablelist::sortByColumn \
        -labelcommand2 tablelist::addToSortColumns \
        -xscrollcommand [list sbs $f.hsb] -yscrollcommand [list sbs $f.vsb] \
        -stripebackground "#f2f4f6" -labelpady 2 -spacing 1 {*}$args

   grid $tbl -row 1 -rowspan 2 -column 1 -sticky news
   catch { grid [$tbl cornerpath] -row 1 -column 2 -sticky ew }
   grid $f.vsb -row 2 -column 2 -sticky ns
   grid $f.hsb -row 3 -column 1 -sticky ew
   grid rowconfigure    $f 2 -weight 1
   grid columnconfigure $f 1 -weight 1

   dict for {col opts} $cols {
      $tbl insertcolumns end 0 $col
      $tbl columnconfigure end -name $col -labelalign center {*}$opts
   }
}

proc make_inputs {f} { 
   global data tbl 

   make_tablelist_frame "tbl" $f $::columns \
        -selectmode multiple -selecttype row  -height 8 \
        -titlecolumns 1 -movablecolumns 1 -exportselection 0 

   foreach {key row} [array get data] { addrow $tbl $key $row }

   $tbl sortbycolumnlist {"#" "val"} {inc inc}

   bind $tbl <<TablelistSelect>> { selection_changed }
   bind [$tbl bodypath] <Double-1> [list toggle_selectable $tbl %y]
   bind [$tbl bodypath] <Control-space> [list toggle_selectable $tbl ""]

   focus $tbl
}
proc make_outputs {f} {
   global tblo out; set out 0.00000000

   set outcols {
      "#" {-align right -showlinenumbers 1 -width 2}
      adr {-align left  -width 35 -editable 1}
      val {-align left  -width 12 -editable 1}
   }

   make_tablelist_frame "tblo" $f $outcols \
        -selectmode browse   -selecttype cell -height 2 \
        -titlecolumns 0 -movablecolumns 1 -exportselection 0 \
        -editendcommand validate_input 

   $tblo insert end {}

   bind [$tblo bodypath] <Double-1> { remove_output %x,%y; reset_click }
   bind [$tblo bodypath] <Delete> { remove_output active }
   bind [$tblo bodypath] <Insert> { add_output ""}
}

proc make_adresses {f} {
   global tbla

   # "#" {-align right -showlinenumbers 1 -width 2}
   set adrcols {
      adr {-align left  -width 35 }
      acc {-align left  -width 20 }
   }

   make_tablelist_frame "tbla" $f $adrcols \
        -selectmode browse   -selecttype cell -height 6 \
        -titlecolumns 0 -movablecolumns 1 -exportselection 1

   $tbla sortbycolumnlist {"acc" "adr"} {dec inc}

   bind [$tbla bodypath] <Double-1> { add_output %y; reset_click }
   bind [$tbla bodypath] <Key-Return> { add_output "active" }

   refresh_addrbook
}

proc make_bottom {f} {
   frame $f 
   lappend entryopts -state readonly -width 12 -justify center 
   lappend entryopts -font TkHeadingFont
   label $f.l1 -text "Sum(Input):"
   entry $f.sum -textvariable sum {*}$entryopts
   label $f.l2 -text "Sum(Output):"
   entry $f.out -textvariable out {*}$entryopts
   label $f.l3 -text "Miner Fee:"
   entry $f.fee -textvariable rest {*}$entryopts
   button $f.create -text "Create TX" \
              -command { create_transaction } -underline 0
   pack $f.create -expand no -fill both -side right
   pack $f.fee -expand yes -fill both -side right
   pack $f.l1 -fill y -expand no -side left
   pack $f.sum -expand yes -fill both -side left
   pack $f.l2 -fill y -expand no -side left
   pack $f.out -expand yes -fill both -side left
   pack $f.l3 -fill y -expand no -side left

   trace add variable ::rest write [list update_fee_window $f]
   update_fee_window $f
}
proc validate_input {tblo row col newval} {
    switch -- $col {
       1 { # adr
           global accounts
           if {[info exists accounts($newval)]} {
               set newval $accounts($newval)
           }
           if {$newval ne "" && ![Base58::checkadr $newval]} {
               $tblo rejectinput
           }
       }
       2 { # val
          catch {set newval [format "%.8f" [expr {abs($newval)}]]}
          after idle output_changed 
       }
    }
    return $newval
}
proc remove_output {idx} {
   global tblo
   if {[string match "*,*" $idx]} {
      lassign [split $idx ","] x y; # x starts with "@"
      incr y [winfo y [$tblo bodypath]]; set idx "@$x,$y"
      lassign [split [$tblo containingcell $x $y] ","] row col
      if {$row < 0 || $col != 0} { return }
   }
   if {[$tblo size] > 1} {
      set row [$tblo index $idx]
      $tblo activate [expr {$row+1<[$tblo size]?$row+1:$row-1}]
      $tblo delete $row
   } else { $tblo rowconfigure end -text "" }
   output_changed
}
proc add_output {y} {
   global tblo tbla; set adr ""

   if {$y ne ""} {;# insert some item from address table
      if {$y eq "active"} {
         set rownum [$tbla index active]
      } else {; # determine item
         incr y [winfo y [$tbla bodypath]]
         set rownum [$tbla index @0,$y]
      }
      if {$rownum ne ""} { set adr [$tbla rowcget $rownum -name] }
   };# else: insert new empty row

   $tblo finishediting; $tblo cancelediting; # if finish not ok then cancel
   set tgt end; set cur [$tblo index active]
   if {$cur ne ""} {
      set cadr [$tblo getcells [list $cur,adr]] 
      if {$cadr eq ""} { set tgt $cur }
   }
   if {$tgt eq "end"} {
      $tblo insert end [list "" $adr ""]
   } else {
      $tblo cellconfigure $cur,adr -text $adr
   }
   if {$adr eq ""} { set col "adr" } else { set col "val" }
   $tblo activatecell $tgt,$col
   $tblo cellselection set $tgt,$col
   $tblo editcell $tgt,$col
   return -code break
}

proc update_fee_window {f args} {
   if {![winfo exists $f.fee] || ![winfo exists $f.create]} {return}
   global rest
   if {$rest eq "" || $rest < 0.0} {
      $f.create conf -state disabled; set color "gray"
   } else {
      $f.create conf -state normal
      if       {$rest < 0.0001} { set color "#ffefdf"
      } elseif {$rest > 0.1}    { set color "#ffaf7f"
      } elseif {$rest > 0.005}  { set color "#ffef7f"
      } elseif {$rest > 0.0005} { set color "#ffffcf"
      } else                    { set color "#dfffdf"
      }
   }
   $f.fee configure -readonlybackground $color
}

proc create_transaction {} {
    global data tbl tblo rest
    if {[$tblo editwinpath] ne ""} {
       if {![ $tblo finishediting ]} { return }; # not with unfinished edits
       output_changed
       if {$rest eq "" || $rest < 0.0} { return }; # all fine after edit?
    }
    set rownums [$tbl curselection]; set inputs ""
    foreach rownum $rownums {
       set key [$tbl rowcget $rownum -name]; set row $data($key)
       set in "\{\"txid\":\"[dict get $row txid]\","
       append in "\"vout\":[dict get $row vout]\}"
       lappend inputs $in
    }
    set rows [$tblo get 0 end]; set outputs ""; set rownum -1
    foreach row $rows { incr rownum
       set adr [string trim [lindex $row 1]]
       set val [string trim [lindex $row 2]]
       if {$adr eq "" && $val eq ""} { continue }
       if {$adr eq "" } { $tblo editcell $rownum,adr; return }
       if {$val eq "" || $val == 0.0} { $tblo editcell $rownum,val; return }
       set out "\"${adr}\":${val}"; lappend outputs $out
    }

    if {[llength $inputs]} {
       set in "\[\n   [join $inputs ",\n   "]\n\]"
    } else { set in "\[\]" }
    if {[llength $outputs]} {
       set out "\{\n   [join $outputs ",\n   "]\n\}"
    } else { set out "\{\}" }

    make_overlay [set f .f.panes.overlay]
    place $f -in .f.panes -x 0 -y 0 -relwidth 1 -relheight 1

    $f.text insert end "Processing transaction...\n\n"

    $f.text insert end "$::btcexe createrawtransaction '$in' '$out'\n\n" 
    update idletasks

    set res [catch { exec $::btcexe createrawtransaction $in $out 2>@1 } result]
    $f.text insert end "$result\n\n"
    if {$res} { $f.text insert end "Failed.\n"; return }
    update idletasks

    set res [catch { exec $::btcexe signrawtransaction $result 2>@1 } result]
    $f.text insert end "$result\n\n"
    if {$res} { $f.text insert end "Failed.\n"; return }
    update idletasks

    set res [catch { json::json2dict $result } txdict]
    if { $res != 0 || [dict size $txdict] != 2 ||
         [dict keys $txdict] ne "hex complete" ||
         [dict get $txdict complete] ne "true"
    } then { $f.text insert end "Failed.\n"; return }
    set signedtx [dict get $txdict "hex"]

    $f.text insert end "$::btcexe sendrawtransaction '$signedtx'\n\n"
        
    button $f.text.yes -text "Send" -command [list finish_tx $f $signedtx 1 ]
    button $f.text.no -text "Cancel" -command [list destroy $f ]
    button $f.text.nobut -text "Don't send, but keep this text open" \
                 -command [list finish_tx $f $signedtx 0 ]

    $f.text window create end -window $f.text.yes
    $f.text window create end -window $f.text.no
    $f.text window create end -window $f.text.nobut
    $f.text insert end "\n"
}
proc finish_tx {f tx send} {
    eval { destroy {*}[winfo children $f.text] }
    
    if {$send} {
       set res [catch { exec $::btcexe sendrawtransaction $tx 2>@1 } result]
       $f.text insert end "$result\n\n"
       if {$res} { $f.text insert end "Failed.\n"; return }
       $f.text insert end "Done. "
    } else {
       $f.text insert end "Not done. "
    }

    $f.text insert end "Click cancel to return to the tables.\n"
    $f.text see end
}

proc tablelist::labelB3Down {w shiftPressed} {
    parseLabelPath $w win col
    upvar ::tablelist::ns${win}::data data
    if {!$data(isDisabled) &&
        $data(-resizablecolumns) && $data($col-resizable)} {
        if {[doColCget $col $win -width] == 0} {
            doColConfig $col $win -width -$data($col-lastStaticWidth)
        } else {
            doColConfig $col $win -width 0
        }
        event generate $win <<TablelistColumnResized>>
    }
}

proc make_overlay {f} {
    frame $f; text $f.text; button $f.cancel; focus $f.text
    pack $f.cancel -side bottom -expand no -fill both
    pack $f.text -side top -expand yes -fill both
    $f.text configure    -wrap char
    $f.cancel configure  -text Cancel -command [list destroy $f ]
}

proc update_rest {} { global sum out rest
    if {$sum <= 0.0 || $out <= 0.0} { set rest ""
    } else { set rest [format %.8f [expr {$sum - $out}]] }
}
proc selection_changed {} {
    global data sum tbl; set sum 0
    foreach rownum [$tbl curselection] {
       set key [$tbl rowcget $rownum -name]
       incr sum [expr {wide(1e8*[dict get $data($key) amount]+.5)}]
    }; set sum [format %.8f [expr {$sum/1e8}]]; update_rest
}
proc output_changed {} {
    global data out tblo; set out 0
    foreach row [$tblo get 0 end] {
       lassign $row nr adr val; if {$val eq ""} {continue}
       catch { incr out [expr {wide(1e8*$val+.5)}] }
    }; set out [format %.8f [expr {$out/1e8}]]; update_rest
}

proc select_all_or_none {} {
   global tbl
   set action [expr {[llength [$tbl curselection]]?"clear":"set"}]
   $tbl selection $action 0 end; selection_changed
}
proc toggle_selectable {tbl y} {
    if {$y ne ""} {; # determine item
       incr y [winfo y [$tbl bodypath]]
       set rownum [$tbl index @0,$y]
       reset_click
    } else { set rownum [$tbl index active] }
    if {$rownum eq ""} { return }
    set flag [$tbl rowcget $rownum -selectable]
    updrow $tbl $rownum [expr {!$flag}]
    selection_changed
    return -code break
}

proc print_selection {} {
   global tbl
   make_overlay [set f .f.panes.overlay]
   place $f -in .f.panes -x 0 -y 0 -relwidth 1 -relheight 1

   $f.text insert end "Selected Coins:\n\n"
   set cursel [$tbl curselection]; set data [$tbl get $cursel]
   if {[llength $cursel] == 1} { set data [list $data] }
   set baseurl "https://blockchain.info/tx/"
   foreach coin $data {
       lassign $coin _ val cf adr id 
       set url "$baseurl[string map {: /} $id]"
       $f.text insert end "$id\n"
       $f.text insert end "\t$url\n"
       $f.text insert end "\t$cf\n"
       $f.text insert end "\t$adr\n"
       $f.text insert end "\t$val\n"
       $f.text insert end "\n"
   }
   $f.text insert end "\n"
}

foreach mod {Alt Control} {
   bind . <$mod-Key-p> { print_selection }
   bind . <$mod-Key-a> { select_all_or_none }
   bind . <$mod-Key-r> { refresh_data }
   bind . <$mod-Key-R> { source $this }
   bind . <$mod-Key-q> { exit }
}

make_gui .f; pack .f -expand yes -fill both

