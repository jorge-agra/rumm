$( A tiny propositional database for the Rumm tests. $)

$c ( ) -> <-> wff |- T. $.
$( $j syntax 'wff'; syntax '|-' as 'wff'; $)

$v ph ps ch &W1 &W2 $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
ww1 $f wff &W1 $.
ww2 $f wff &W2 $.

wi $a wff ( ph -> ps ) $.
wb $a wff ( ph <-> ps ) $.
wtru $a wff T. $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

$( Definition of the truth constant. $)
df-tru $a |- ( T. <-> ( ph -> ph ) ) $.

$( Targets of the tests. $)
dfinst $p |- ( T. <-> ( ( ph -> ps ) -> ( ph -> ps ) ) ) $= ? $.
dftru $p |- ( T. <-> ( ph -> ph ) ) $= ? $.
${
  cyc.1 $e |- ph $.
  cyc $p |- ps $= ? $.
$}
${
  panics.1 $e |- ph $.
  panics.2 $e |- ( ph -> ps ) $.
  panics $p |- ps $= ? $.
$}
