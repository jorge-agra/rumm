$( A tiny database with wff and class terms for the Rumm metavariable tests.
   It declares no metavariable: Rumm declares `&W1`, `&C1`... itself. $)

$c ( ) -> = wff class |- c0 c1 $.
$( $j syntax 'wff'; syntax 'class'; syntax '|-' as 'wff'; $)

$v ph ps A B $.
wph $f wff ph $.
wps $f wff ps $.
cA $f class A $.
cB $f class B $.

wi $a wff ( ph -> ps ) $.
wceq $a wff A = B $.
cc0 $a class c0 $.
cc1 $a class c1 $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
eqid $a |- A = A $.
id $a |- ( ph -> ph ) $.

$( Targets of the tests. $)
c0id $p |- c0 = c0 $= ? $.
c1id $p |- c1 = c1 $= ? $.
idth $p |- ( ph -> ph ) $= ? $.
