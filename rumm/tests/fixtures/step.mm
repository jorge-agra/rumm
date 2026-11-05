$( A small propositional database for the stepwise tests: syllogism, identity, modus ponens. $)

$c ( ) -> wff |- $.
$( $j syntax 'wff'; syntax '|-' as 'wff'; $)

$v ph ps ch th $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.

wi $a wff ( ph -> ps ) $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

${
  mp2.1 $e |- ph $.
  mp2.2 $e |- ps $.
  mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
  mp2 $p |- ch $= ? $.
$}

${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $= ? $.
$}

${
  syl.1 $e |- ( ph -> ps ) $.
  syl.2 $e |- ( ps -> ch ) $.
  syl $p |- ( ph -> ch ) $= ? $.
$}

id $p |- ( ph -> ph ) $= ? $.

$( Targets of the tests. $)
${
  sylex.1 $e |- ( ph -> ps ) $.
  sylex.2 $e |- ( ps -> ch ) $.
  sylex $p |- ( ph -> ch ) $= ? $.
$}
${
  syl3.1 $e |- ( ph -> ps ) $.
  syl3.2 $e |- ( ps -> ch ) $.
  syl3.3 $e |- ( ch -> th ) $.
  syl3 $p |- ( ph -> th ) $= ? $.
$}
