$( CC0. Excerpt of set.mm, maintained by the Metamath contributors. $)
$c ( $.
  $c ) $.
  $c -> $.
  $c wff $.
  $c |- $.
  $v ph $.
  $v ps $.
  $v ch $.
  $v th $.
  $v ta $.
  $v et $.
  $v ze $.
  $v si $.
  $v rh $.
  $v mu $.
  $v la $.
  $v ka $.
  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.
  wze $f wff ze $.
  wsi $f wff si $.
  wrh $f wff rh $.
  wmu $f wff mu $.
  wla $f wff la $.
  wka $f wff ka $.
  wi $a wff ( ph -> ps ) $.
  ${
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.
    ax-mp $a |- ps $.
  $}
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
  ${
    a1i.1 $e |- ph $.
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
  $}
