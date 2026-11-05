$( Include set.mm $)
$[ ../../set.mm/set.mm $]

$( The example theorems for Rumm. The database is plain: the metavariables of the
   scripts (`&W1`, `&C1`...) are declared by Rumm, not here. $)

${
  rummex1.1 $e |- D e. RR $.
  rummex1.2 $e |- D =/= 0 $.
  $( Example theorem to be proven using Rumm $)
  rummex1 $p |- ( ( ( A e. RR /\ B e. RR ) /\ C e. RR )
                    -> ( -u A x. ( ( B - C ) / D ) ) e. RR ) $=
    ( cr wcel wa cneg cmin cdiv simpll renegcld simplr simpr resubcld a1i cc0
      co wne redivcld remulcld ) AGHZBGHZIZCGHZIZAJBCKTZDLTUHAUDUEUGMNUHUIDUHBC
      UDUEUGOUFUGPQDGHUHERDSUAUHFRUBUC $.
$}

${
    isleag2lem.p $e |- P = ( Base ` G ) $.
    isleag2lem.g $e |- ( ph -> G e. TarskiG ) $.
    isleag2lem.a $e |- ( ph -> A e. P ) $.
    isleag2lem.b $e |- ( ph -> B e. P ) $.
    isleag2lem.c $e |- ( ph -> C e. P ) $.
    isleag2lem.d $e |- ( ph -> D e. P ) $.
    isleag2lem.e $e |- ( ph -> E e. P ) $.
    isleag2lem.f $e |- ( ph -> F e. P ) $.
    isleag2lem.1 $e |- ( ph -> <" A B C "> ( leA ` G ) <" D E F "> ) $.
    $( Geometrical "less than" property for angles: another equivalent
       definition. Theorem 11.29 of [Schwabhauser] p. 102.  (Contributed by
       Thierry Arnoux, 17-Oct-2020.) $)
    isleag2lem $p |- ( ph -> E. y e. P ( C ( inA ` G ) <" A B y ">
        /\ <" A B y "> ( cgrA ` G ) <" D E F "> ) ) $=
      ? $.
$}

