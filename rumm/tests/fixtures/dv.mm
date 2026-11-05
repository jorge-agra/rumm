$( A tiny predicate database for the Rumm `$d` and database order tests. $)

$c ( ) -> = A. wff setvar |- $.
$( $j syntax 'wff'; syntax 'setvar'; syntax '|-' as 'wff'; $)

$v ph ps x y z $.
wph $f wff ph $.
wps $f wff ps $.
vx $f setvar x $.
vy $f setvar y $.
vz $f setvar z $.

wi $a wff ( ph -> ps ) $.
weq $a wff x = y $.
wal $a wff A. x ph $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

${
  $d x ph $.
  $( Needs `x` and `ph` disjoint. $)
  ax-5 $a |- ( ph -> A. x ph ) $.
$}

$( Another route to the same shape, which needs no `$d`: a stand-in for the
   alternative of a `try` (the statement is a toy, not sound). $)
ax-5alt $a |- ( ph -> A. x ph ) $.

$( The `$d` is declared by the theorem. $)
${
  $d x ph $.
  dvok $p |- ( ph -> A. x ph ) $= ? $.
$}

$( No `$d` declared: citing `ax-5` is a violation. $)
dvbad $p |- ( ph -> A. x ph ) $= ? $.

$( `x` occurs in the expression for `ph`, so `ax-5` can't be used even though the theorem
   declares `$d x y`. $)
${
  $d x y $.
  dvshared $p |- ( x = y -> A. x x = y ) $= ? $.
$}

$( Database order: `later` comes after `earlier`, and has the same statement. $)
earlier $p |- ( ph -> ph ) $= ? $.
later $p |- ( ph -> ph ) $= ? $.
