USING:
tim.heap tim.stack utils
assocs kernel accessors
sequences locals
math math.functions
lists lists.lazy
inverse arrays fry prettyprint ;
IN: tim

! *********
! 3 Instruction Machine Language  (machine actions)
TUPLE: take n ;
C: <take> take
TUPLE: enter tim-addr ;
C: <enter> enter
TUPLE: push tim-addr ;
C: <push> push
TUPLE: pushv value-addr ;
C: <pushv> pushv

SINGLETON: return
TUPLE: binop prim ;
C: <binop> binop
TUPLE: unop prim ;
C: <unop> unop

! TUPLE: cond { conseq instr-seq } { alt instr-seq } ;
TUPLE: cond conseq alt ;
C: <cond> cond

! *******************
! Tim Address Modes
TUPLE: arg nth ;
C: <arg> arg
TUPLE: label name ;
C: <label> label
TUPLE: code instr-seq ;
C: <code> code
TUPLE: const val ;
C: <const> const

! *******************
! Value Address Modes

TUPLE: const-val val ;
C: <const-val> const-val
SINGLETON: frameptr

! *************
! Frame Ptr objects

TUPLE: frame-addr addr ;
C: <frame-addr> frame-addr
TUPLE: frame-int nth ;
C: <frame-int> frame-int
SINGLETON: framenull

! **************
! Core Language (primitive instructions syntax)

! expressions
TUPLE: evar name ;
C: <evar> evar
TUPLE: enumb n ;
C: <enumb> enumb
TUPLE: estring str ;
C: <estring> estring
TUPLE: econstr tag arity ;
C: <econstr> econstr
TUPLE: eap e1 e2 ;
C: <eap> eap
TUPLE: elet isrec defns body ;
C: <elet> elet
TUPLE: ecase expr alts ;
C: <ecase> ecase
TUPLE: elambda args body ;
C: <elambda> elambda

! **************
! 3 Instruction Machine Spec

! cstore (codestore) is analagous to labels from sicp.chp5
! pc and fp are simpler registers

! pc is a list of instructions
! fp is a frame-address 
! TUPLE: tim { pc cons } { fp frame-addr } { stack cons } heap { cstore assoc } ;
TUPLE: tim pc fp astack vstack dump heap cstore stats ;
C: <tim> tim

: halted? ( tim -- bool ) pc>> nil? ;

: vpop ( machine -- obj )
    vstack>> spop nip ;

: apop ( machine -- obj )
    astack>> spop nip ;

: vpush ( elem machine -- machine )
    [ vstack>> spush drop ] keep ; 

: apush ( elem machine -- machine )
    [ astack>> spush drop ] keep ;

TUPLE: closure fp pc ;
C: <closure> closure

: int-code ( -- instr-list )
     frameptr <pushv> return 2list ;

: load-closure ( machine closure -- machine )
     [ <closure> ] undo [ >>fp ] [ >>pc ] bi-curry* bi drop ;

TUPLE: stat-machine ;
C: <stat-machine> stat-machine

! ***************
! Frame Manipulations

! frames are lists of closures (as usual)

: falloc ( heap obj -- address )
   halloc <frame-addr> ;

! make sure not off by 1
: fget ( arg fp heap -- closure )
   [ [ <frame-addr> ] undo ] dip hlookup
   [ 1 - ] dip lnth ;

! off by 1 garbage, going by book now, but redo later
:: fupdate ( heap addr n closure  -- )
   addr heap hlookup :> frame
   closure n 1 - frame insert-nth
   addr heap hupdate ;

: lookup ( name cstore -- instr-seq )
    over '[ _ " not present -- Code Lookup" append throw ]
    [ at ] dip unless* ;

! converts a machine and  address mode into a closure
GENERIC: >closure ( machine tim-addr -- closure )

M: arg >closure ( machine arg -- closure )
   nth>> swap [ fp>> heap>> ] fcleave fget ; inline

M: code >closure ( machine code -- closure )
   [ fp>> ] [ instr-seq>> ] bi* <closure> ;

M:: label >closure ( machine label -- closure )
   machine fp>>
   label name>> machine cstore>> at
   <closure> ;

M: const >closure ( machine inst -- closure )
   nip val>> int-code <closure> ;

! ***********
! Evaluator

! not working
! confused about pc fp steps, advancing the pc, etc.

GENERIC: step ( machine instr -- machine )

! haskell does this in 4 lines total - have to do better
! n optimize llength call later
! lcut here has been meticoulously combed over against the spec: 1 times

! takes the top n elements off the arg stack, forms a new frame f, and makes the fp point to f
M: take step ( machine take -- machine )
   [let* | n [ n>> ]
           m [ ]
           astack [ m astack>> ]
           heap [ m heap>> ]  |
       astack depth>> n <
       [ n astack s>> list>array [ . ] bi@ "too few args for TAKE instr" throw ]
       [ n astack spop-n
         heap swap falloc
         m swap >>fp 
       ]
   ] if ;

: fetch-closure ( machine addr-mode -- machine closure )
    dupd tim-addr>> >closure ;

M: enter step ( machine enter -- machine )
    fetch-closure load-closure ;

M: push step ( machine push -- machine )
    fetch-closure swap apush ; inline

! "-" <evar> 5 <evar> <eap> 6 <evar> <eap>

! having trouble with this one.  want to avoid tedium for binary operator state
! transistion rules.  I've run into this issue before
M:: binop step ( machine binop -- machine )
    machine [ vpop ] dup bi swap  ! careful of ordering for primitive
    binop prim>> call
    machine vpush ; inline

! push the current fp onto the vstack
M: pushv step ( machine pushv -- machine )
    drop dup fp>> swap vpush ; inline

! pop and load the top closure off the argstack
M: return step ( machine return -- machine )
   drop dup apop load-closure ; inline

M: cond step ( machine cond -- machine )
    over vpop zero?
    [ conseq>> ]
    [ alt>> ] ? change-pc ; inline

: do-admin ( m -- m )
   ;

! instead of having a top level control loop, you could have the tim instructions
! call the next instr but would this mean more code?

: advance-pc ( machine -- machine instr )
    [ uncons ] change-pc swap ;

! the treewalker
! but generics help flatten the tree from this contol perspective
: eval ( machine -- )
   [ halted? ]
   [ advance-pc step do-admin drop ]
   bi-curry until ; inline

! ****************
! Compiler

TUPLE: supercomb name args body ;
: <sc> ( n a b -- supercomb ) supercomb boa ;

! fac is too complicated to do without a parser

! there is a better way to say this
: prelude-defs ( -- array )
     { [ "I" { "x" } "x" <evar> ]
       [ "K" { "x" "y" } "x" <evar> ]
       [ "K1" { "x" "y" } "y" <evar> ]
       [ "S" { "f" "g" "x" } 
         "f" "x" [ <evar> ] bi@ <eap>
         "g" "x" [ <evar> ] bi@ <eap> <eap> ]
       [ "compose" { "f" "g" "x" }
         "f" <evar>
         "g" <evar> "x" <evar> <eap>
         <eap> ]
       [ "compose2" { "f" "g" "x" }
         "f" <evar>
         "g" <evar>
         "x" <evar> <eap>
         "x" <evar> <eap> <eap> ]
       [ "+1" { "x" } "+" <evar> "x" <evar> <eap> 1 <enumb> <eap> ]

     } [ call <sc> ] map  ; inline

! ****************
! Compilation Sections

! should compile be generic?

:: compile-biprim ( quot -- instr-seq )
     2 <take>
     quot <binop> return 2list <code> <push>
     1 <arg> <enter>
     2list <code> <push>
     2 <arg> <enter> 3list ;

! i think this is right 
! : t-if ( intr-seq instr-seq -- instr-seq )
!     3 <take>
!     1 <arg> <enter>
!     2 <arg> <enter> 1list
!     3 <arg> <enter> 1list
!     <cond> 3list ;

: compiled-prims ( -- seq )
    {  "+" [ + ]
       "-" [ - ]
       "*" [ * ]
       "/" [ / ]
       "^" [ ^ ]
     } 2 nsplit [ compile-biprim ] assoc-map ; foldable

DEFER: compile-r

GENERIC: compile-a ( env obj -- tim-addr )

 ! not sure about this first case
M: eap compile-a 
     compile-r <code> ; inline 

M:: evar compile-a ( env evar -- tim-addr )
   evar name>> env at [ "unknown variable: " evar name>> append throw ] unless* ; inline 

M: enumb compile-a 
     [ <enumb> ] undo <const> nip ; inline

M: estring compile-a 
     [ <estring> ] undo <const> nip ; inline
 
GENERIC: compile-r ( env expr -- instr-seq )

! doesn't compile
 M: eap compile-r
 [ <eap> ] undo
 [ compile-r ]
 [ compile-a <push> ] bi-curry* bi swons ; inline 

M: evar compile-r
    compile-a <enter> 1list ; inline

M: enumb compile-r
    compile-a <enter> 1list ; inline

! WANTED: want list>array treewalker aka pretty printer

!  WANTED: destructuring macro 
:: compile-sc ( env sc -- name/instr-list )
    [let | name [ sc name>> ]
           args [ sc args>> ]
           body [ sc body>> ] |
        args sequence>list 
        1 lfrom [ <arg> ] lazy-map
        lzip list>array env append
        body compile-r
        
        args length <take>
        swons
        
        name swap 2array ] ;

! compile a user program into a table of sc's names
! and their associated compiled code          
: >cstore ( program -- sc-table )
    prelude-defs append
    dup [ name>> dup <label> 2array ] map
    compiled-prims [ first dup <label> 2array ] map append
    '[ _ swap compile-sc ] map
    compiled-prims append
    ; inline

: <pc> ( -- pc ) "main" <label> <enter> 1list ; foldable
: <fp> ( -- fp ) framenull ; foldable
          
: <astack> ( -- stack )
    framenull nil <closure>
    <stack> spush ; foldable

: <vstack> ( -- vstack ) <stack> ; foldable                 
: <dump> ( -- dump ) <stack> ; foldable
          
:: compile ( program -- machine )
    <pc>
    <fp>
    <astack>
    <vstack>
    <dump>
    <heap>
    program >cstore
    <stat-machine>
    <tim> ; inline

! ***********
! running          

! final results (ints only) are stored in fp in mk.1    
: run-prog ( sc-seq -- string )
    compile dup eval vstack>> s>> list>array ; inline

! ***********
! Sample Programs

: main1 ( -- seq )
    "main" { }
    "S" <evar>
    "K" <evar> <eap>
    "K" <evar> <eap>
    200  <enumb> <eap>
    <sc> 1array ; 

: main2 ( -- seq )
    "main" { } "I" <evar> 2 <enumb> <eap> <sc> 1array ;

: main3 ( -- seq )
    "main" { } 100 <enumb> <sc> 1array ;

: main4 ( -- seq )
    "main" { } "+" <evar> 5 <enumb> <eap> 3 <enumb> <eap> <sc> 1array ;

: main5 ( -- seq )
    "main" { } "K" <evar> 100 <enumb> <eap> "S" <evar> <eap> <sc> 1array ;

: main6 ( -- seq )
    "main" { } "+1" <evar> 1001 <enumb> <eap> <sc> 1array ;
    

