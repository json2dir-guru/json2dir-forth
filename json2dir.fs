\ json2dir: create the directory tree a JSON document describes, in the current directory.
\ Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
\ Gforth only: ANS words, plus Gforth's C interface for the POSIX calls ANS Forth has no words for.
\ Usage: gforth json2dir.fs -e bye < document.json

\ ---- POSIX calls through Gforth's C interface ----

c-library json2dir_forth
\c #include <sys/types.h>
\c #include <sys/stat.h>
\c #include <fcntl.h>
\c #include <unistd.h>
c-function c-open    open    a n n -- n
c-function c-close   close   n -- n
c-function c-write   write   n a n -- n
c-function c-mkdir   mkdir   a n -- n
c-function c-symlink symlink a a -- n
c-function c-fchmod  fchmod  n n -- n
c-function c-fchdir  fchdir  n -- n
c-function c-umask   umask   n -- n
end-c-library

\ open(2) flags, Linux x86-64 values
0        constant O_RDONLY
1        constant O_WRONLY
$40      constant O_CREAT
$80      constant O_EXCL
$10000   constant O_DIRECTORY
$20000   constant O_NOFOLLOW
$80000   constant O_CLOEXEC
$200000  constant O_PATH

\ ---- errors: a message (and optionally the name it is about), then THROW ----

2variable err-msg
2variable err-name
: fail ( a u -- ) err-msg 2! 0 0 err-name 2! 1 throw ;
: fail-at ( name-a name-u msg-a msg-u -- ) err-msg 2! err-name 2! 1 throw ;
: say ( a u -- ) stderr write-file drop ;

\ ---- read all of stdin ----

variable buf  variable blen  variable bcap
: read-input ( -- )
  65536 bcap !  bcap @ allocate throw buf !  0 blen !
  begin
    blen @ bcap @ = if bcap @ 2* bcap !  buf @ bcap @ resize throw buf ! then
    buf @ blen @ +  bcap @ blen @ -  stdin read-file throw
  dup while blen +! repeat drop ;

\ ---- strict UTF-8 check ----

: bad-utf8 ( -- ) s" input is not valid UTF-8" fail ;
\ For a lead byte: number of continuation bytes and the allowed range of the first one.
: lead ( c -- n lo hi )
  dup $80 < if drop 0 0 0 exit then
  dup $C2 $E0 within if drop 1 $80 $BF exit then
  dup $E0 = if drop 2 $A0 $BF exit then
  dup $ED = if drop 2 $80 $9F exit then
  dup $E1 $F0 within if drop 2 $80 $BF exit then
  dup $F0 = if drop 3 $90 $BF exit then
  dup $F4 = if drop 3 $80 $8F exit then
  dup $F1 $F4 within if drop 3 $80 $BF exit then
  drop bad-utf8 0 0 0 ;
: check-char ( p end -- p' ) { p end }
  p c@ lead { n lo hi }
  p 1+ n + end > if bad-utf8 then
  n if
    p 1+ c@ lo hi 1+ within 0= if bad-utf8 then
    n 1 ?do p 1+ i + c@ $80 $C0 within 0= if bad-utf8 then loop
  then
  p 1+ n + ;
: utf8-check ( a u -- ) over + { end } begin dup end < while end check-char repeat drop ;

\ ---- JSON parser: values become nodes ----
\ node = 3 cells: type, x, y.  string: 1 addr len.  object: 2 vec 0.  array: 3 vec 0.
\ vec = 3 cells: count, capacity, data (cells).  An object's vec holds len, addr, node per member.

: node3 ( type x y -- node ) 3 cells allocate throw { t x y n } t n !  x n cell+ !  y n 2 cells + !  n ;
: ntype ( node -- t ) @ ;
: nvec ( node -- vec ) cell+ @ ;
: str@ ( node -- a u ) dup cell+ @ swap 2 cells + @ ;
: vec-new ( -- v ) 3 cells allocate throw { v }  0 v !  8 v cell+ !  8 cells allocate throw v 2 cells + !  v ;
: vec-count ( v -- n ) @ ;
: vec-data ( v -- a ) 2 cells + @ ;
: vec-push ( x v -- ) { x v }
  v @ v cell+ @ = if
    v cell+ @ 2* v cell+ !  v vec-data v cell+ @ cells resize throw v 2 cells + !
  then
  x v vec-data v @ cells + !  1 v +! ;

variable pos  variable lim
: bad-json ( -- ) s" input is not valid JSON" fail ;
: more? ( -- f ) pos @ lim @ < ;
: peek ( -- c ) more? if pos @ c@ else -1 then ;
: advance ( -- ) 1 pos +! ;
: skip-ws ( -- ) begin peek dup 32 = over 9 = or over 10 = or swap 13 = or while advance repeat ;
: expect-char ( c -- ) peek <> if bad-json then advance ;

variable op   \ output pointer while decoding a string
: put ( c -- ) op @ c!  1 op +! ;
: put-utf8 ( cp -- )
  dup $80 < if put exit then
  dup $800 < if dup 6 rshift $C0 or put  $3F and $80 or put exit then
  dup $10000 < if dup 12 rshift $E0 or put  dup 6 rshift $3F and $80 or put  $3F and $80 or put exit then
  dup 18 rshift $F0 or put  dup 12 rshift $3F and $80 or put
  dup 6 rshift $3F and $80 or put  $3F and $80 or put ;

: hexdigit ( c -- n )
  dup [char] 0 [char] 9 1+ within if [char] 0 - exit then
  dup [char] a [char] f 1+ within if [char] a - 10 + exit then
  dup [char] A [char] F 1+ within if [char] A - 10 + exit then
  drop bad-json 0 ;
: hex4 ( -- n ) pos @ 4 + lim @ > if bad-json then
  0 4 0 do 16 * pos @ c@ hexdigit + advance loop ;
: lone ( -- ) s" string contains an unpaired surrogate" fail ;
: low-surrogate ( hi -- cp )
  pos @ 2 + lim @ > if lone then
  pos @ c@ [char] \ <>  pos @ 1+ c@ [char] u <> or if lone then
  2 pos +!  hex4 dup $DC00 $E000 within 0= if lone then
  $DC00 -  swap $D800 - 10 lshift +  $10000 + ;
: parse-escape ( -- ) \ pos is just after the backslash
  more? 0= if bad-json then  pos @ c@ advance
  case
    [char] " of [char] " put endof
    [char] \ of [char] \ put endof
    [char] / of [char] / put endof
    [char] b of 8 put endof
    [char] f of 12 put endof
    [char] n of 10 put endof
    [char] r of 13 put endof
    [char] t of 9 put endof
    [char] u of hex4
      dup $D800 $DC00 within if low-surrogate else dup $DC00 $E000 within if lone then then
      put-utf8 endof
    bad-json
  endcase ;
\ Bytes up to the closing quote: an upper bound for the decoded length.
: str-span ( -- u )
  pos @ begin dup lim @ >= if bad-json then dup c@ [char] " <> while
    dup c@ [char] \ = if 1+ then 1+
  repeat pos @ - ;
: parse-string ( -- a u ) \ pos is at the opening quote
  advance  str-span 1 max allocate throw dup op ! { start }
  begin peek dup [char] " <> while
    dup 32 < if bad-json then
    advance  dup [char] \ = if drop parse-escape else put then
  repeat drop advance
  start op @ start - ;

defer parse-value ( depth -- node )
: parse-object ( depth -- node ) \ pos is at {
  advance vec-new { d v }  skip-ws
  peek [char] } = if advance 2 v 0 node3 exit then
  begin
    skip-ws  peek [char] " <> if bad-json then
    parse-string v vec-push v vec-push
    skip-ws [char] : expect-char
    d 1+ parse-value v vec-push
    skip-ws peek [char] , =
  while advance repeat
  [char] } expect-char  2 v 0 node3 ;
: parse-array ( depth -- node ) \ pos is at [
  advance vec-new { d v }  skip-ws
  peek [char] ] = if advance 3 v 0 node3 exit then
  begin
    d 1+ parse-value v vec-push
    skip-ws peek [char] , =
  while advance repeat
  [char] ] expect-char  3 v 0 node3 ;
:noname ( depth -- node )
  dup 1000 > if s" document is nested too deeply" fail then
  skip-ws peek
  dup [char] { = if drop parse-object exit then
  dup [char] [ = if drop parse-array exit then
  dup [char] " = if 2drop parse-string 1 -rot node3 exit then
  2drop s" invalid JSON, or a number, true, false or null (not allowed)" fail 0 ;
is parse-value

: parse-doc ( a u -- node )
  over + lim ! pos !
  lim @ pos @ - 3 >= if pos @ 3 s\" \xEF\xBB\xBF" str= if 3 pos +! then then  \ optional BOM
  skip-ws peek [char] { <> if s" the root of the document must be an object" fail then
  0 parse-value  skip-ws more? if s" trailing data after the JSON value" fail then ;

\ ---- validation of the whole document ----

: has-byte? ( a u c -- f ) { c } false -rot bounds ?do i c@ c = or loop ;
: check-name ( a u -- )
  2dup 2dup s" ." str= >r 2dup s" .." str= >r dup 0= >r
  2dup [char] / has-byte? >r 0 has-byte? r> or r> or r> or r> or
  if s" invalid name" fail-at then 2drop ;

: rec ( data i -- addr ) 3 * cells + ;
create tmp 3 cells allot
: rec-swap ( r1 r2 -- ) { r1 r2 } r1 tmp 3 cells move  r2 r1 3 cells move  tmp r2 3 cells move ;
: rec-gt? ( r -- f ) dup 3 cells - 2@ rot 2@ compare 0> ;
: sift ( r0 r -- ) begin 2dup u< while dup rec-gt? while dup 3 cells - over rec-swap 3 cells - repeat then 2drop ;
\ Members in ascending order of the UTF-8 bytes of their names; duplicates are rejected.
: sort-members ( data n -- ) { d n }
  n 2 < if exit then
  n 1 ?do d d i rec sift loop
  n 1 ?do d i 1- rec 2@ d i rec 2@ 2over 2over str= if 2drop s" duplicate name" fail-at then 2drop 2drop loop ;

: no-nul ( a u -- ) 2dup 0 has-byte? if s" a link target cannot contain NUL" fail-at then 2drop ;
defer validate ( node -- )
: validate-array ( node -- )
  nvec dup vec-count 2 <> if drop s\" an array must be [\"link\", target] or [\"script\", content]" fail then
  vec-data { d }
  d @ ntype 1 <>  d cell+ @ ntype 1 <> or if s" an array must hold two strings" fail then
  d @ str@ s" link" str= if d cell+ @ str@ no-nul exit then
  d @ str@ s" script" str= 0= if d @ str@ s" unknown array kind" fail-at then ;
: validate-object ( node -- )
  nvec dup vec-data swap vec-count 3 / { d n }
  d n sort-members
  n 0 ?do d i rec 2@ check-name  d i rec 2 cells + @ validate loop ;
:noname ( node -- )
  dup ntype 2 = if validate-object exit then
  dup ntype 3 = if validate-array exit then
  drop ;
is validate

\ ---- creating the tree ----

variable filemode   \ 0666 & ~umask
: >cz ( a u -- z ) dup 1+ allocate throw { a u z }  a z u move  0 z u + c!  z ;

\ 0 = nothing there, 1 = a real directory, 2 = anything else (a symlink is never followed)
: kind ( z -- k )
  dup O_PATH O_NOFOLLOW or O_DIRECTORY or O_CLOEXEC or 0 c-open
  dup 0>= if c-close drop drop 1 exit then drop
  O_PATH O_NOFOLLOW or O_CLOEXEC or 0 c-open
  dup 0>= if c-close drop 2 exit then drop 0 ;

: write-all ( fd a u name-a name-u -- ) { fd a u na nu }
  begin u 0> while
    fd a u c-write dup 0< if na nu s" cannot write" fail-at then
    dup a + to a  u swap - to u
  repeat ;
: make-file ( name-a name-u z a u exec? -- ) { na nu z a u x }
  z O_WRONLY O_CREAT or O_EXCL or O_NOFOLLOW or O_CLOEXEC or 438 c-open { fd }
  fd 0< if na nu s" cannot create file" fail-at then
  fd a u na nu write-all
  x if fd filemode @ $49 or c-fchmod 0< if na nu s" cannot chmod" fail-at then then
  fd c-close 0< if na nu s" cannot close" fail-at then ;

: remove ( name-a name-u k -- ) \ k from KIND
  dup 1 = if drop s" a directory is in the way" fail-at then
  2 = if 2dup delete-file if s" cannot remove" fail-at then then 2drop ;

defer apply ( node -- )
: enter ( name-a name-u z node -- ) { na nu z node }
  s" ." >cz O_RDONLY O_DIRECTORY or O_CLOEXEC or 0 c-open { parent }
  z O_RDONLY O_DIRECTORY or O_NOFOLLOW or O_CLOEXEC or 0 c-open { fd }
  fd 0< parent 0< or if na nu s" cannot open directory" fail-at then
  fd c-fchdir 0< if na nu s" cannot enter directory" fail-at then
  node apply
  parent c-fchdir 0< if na nu s" cannot leave directory" fail-at then
  fd c-close drop  parent c-close drop ;
: apply-member ( name-a name-u node -- ) { na nu node }
  na nu >cz { z }  z kind { k }
  node ntype 1 = if na nu k remove  na nu z node str@ false make-file exit then
  node ntype 3 = if
    na nu k remove
    node nvec vec-data { d }
    d @ str@ s" link" str= if
      d cell+ @ str@ >cz z c-symlink 0< if na nu s" cannot create symlink" fail-at then
    else na nu z d cell+ @ str@ true make-file then
    exit
  then
  k 1 <> if
    k 2 = if na nu k remove then
    z 511 c-mkdir 0< if na nu s" cannot create directory" fail-at then
  then
  na nu z node enter ;
:noname ( node -- )
  nvec dup vec-data swap vec-count 3 / { d n }
  n 0 ?do d i rec 2@  d i rec 2 cells + @ apply-member loop ;
is apply

\ ---- main ----

: no-args? ( -- f ) \ "gforth json2dir.fs -e bye" leaves "-e bye" in the arguments
  argc @ 1 = if true exit then
  argc @ 3 = if 1 arg s" -e" str=  2 arg s" bye" str= and exit then
  false ;
: run ( -- )
  read-input  buf @ blen @ utf8-check
  buf @ blen @ parse-doc  dup validate  apply ;
: main ( -- )
  no-args? 0= if s\" usage: json2dir < document.json\n" say 2 (bye) then
  0 c-umask dup c-umask drop invert 438 and filemode !
  ['] run catch ?dup if
    s" json2dir: " say
    1 = if
      err-name 2@ dup if say s" : " say else 2drop then  err-msg 2@ say
    else s" internal error" say then
    s\" \n" say 1 (bye)
  then
  0 (bye) ;
main
