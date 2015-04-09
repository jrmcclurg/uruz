" Vim syntax file
" Language   : Parser Generator Generator (PGG)
" (based on the Scala plugin code by Stefan Matthias Aust et al.)
" (also uses http://vim.wikia.com/wiki/Different_syntax_highlighting_within_regions_of_a_file)

if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

syn case match
syn sync minlines=50

function! TextEnableCodeSnip(filetype,start,end,start2,end2,pattern,textSnipHl,thename,thename2) abort
  let ft=toupper(a:filetype)
  let group='textGroupMatch'.a:thename
  if exists('b:current_syntax')
    let s:current_syntax=b:current_syntax
    " Remove current syntax definition, as some syntax files (e.g. cpp.vim)
    " do nothing if b:current_syntax is defined.
    unlet b:current_syntax
  endif
  execute 'syntax include @'.group.' syntax/'.a:filetype.'.vim'
  try
    execute 'syntax include @'.group.' after/syntax/'.a:filetype.'.vim'
  catch
  endtry
  if exists('s:current_syntax')
    let b:current_syntax=s:current_syntax
  else
    unlet b:current_syntax
  endif
  execute 'syntax region ocamlMatch'.a:thename.'
  \ matchgroup='.a:textSnipHl.'
  \ start="'.a:start.'" end="'.a:end.'"
  \ contained nextgroup=uruzType,ocamlMatchCode skipwhite
  \ contains=@'.group
  execute 'syntax region ocamlMatch'.a:thename2.'
  \ matchgroup='.a:textSnipHl.'
  \ start="'.a:start2.'" end="'.a:end2.'"
  \ contained nextgroup=uruzType,ocamlMatchCode skipwhite
  \ contains=@'.group
  execute 'syntax match ocamlKey'.a:thename2.'
  \ "'.a:pattern.'"
  \ contained nextgroup=uruzType,ocamlMatchCode skipwhite
  \ contains=@'.group
endfunction

call TextEnableCodeSnip('ocaml', '{', '}', '(', ')', '[a-zA-Z0-9_~.]\+', 'SpecialComment', 'Code', 'Type')
"call TextEnableCodeSnip('ocaml', '(', ')', 'SpecialComment', 'Type')
"call TextEnableCodeSnip2('ocaml', '[a-zA-Z0-9_~.]\+', 'SpecialComment', 'Type')

" most keywords
syn keyword uruzKeyword property keyword token eof nextgroup=uruzType,ocamlMatchCode skipwhite
"syn match uruzKeyword "=>"
"syn match uruzKeyword "<-"
"syn match uruzKeyword "\<_\>"

"syn match uruzOperator ":\{2,\}" "this is not a type
"
"" package and import statements
"syn keyword uruzPackage package nextgroup=uruzFqn skipwhite
"syn keyword uruzImport import nextgroup=uruzFqn skipwhite
"syn match uruzFqn "\<[._$a-zA-Z0-9,]*" contained nextgroup=uruzFqnSet
"syn region uruzFqnSet start="{" end="}" contained
"
"" boolean literals
syn keyword uruzBoolean true false nextgroup=uruzType,ocamlMatchCode skipwhite
"
"" definitions
syn keyword uruzDef parser lexer ast nextgroup=uruzDefName skipwhite
"syn keyword uruzVal val nextgroup=uruzValName skipwhite
"syn keyword uruzVar var nextgroup=uruzVarName skipwhite
"syn keyword uruzClass class nextgroup=uruzClassName skipwhite
"syn keyword uruzObject object nextgroup=uruzClassName skipwhite
"syn keyword uruzTrait trait nextgroup=uruzClassName skipwhite
syn match uruzDefName "[a-zA-Z0-9_~]\+" nextgroup=ocamlMatchCode,uruzType,uruzEqOp skipwhite
syn match uruzAnnotName "@[a-zA-Z0-9_]\+" nextgroup=ocamlMatchCode skipwhite
"syn match uruzValName "[^ =:;([]\+" contained
"syn match uruzVarName "[^ =:;([]\+" contained 
"syn match uruzClassName "[^ =:;(\[]\+" contained nextgroup=uruzClassSpecializer skipwhite
"syn region uruzDefSpecializer start="\[" end="\]" contained contains=uruzDefSpecializer
"syn region uruzClassSpecializer start="\[" end="\]" contained contains=uruzClassSpecializer
"
"" type constructor (actually anything with an uppercase letter)
"syn match uruzConstructor "\<[A-Z][_$a-zA-Z0-9]*\>" nextgroup=uruzConstructorSpecializer
"syn region uruzConstructorSpecializer start="\[" end="\]" contained contains=uruzConstructorSpecializer
"
"" method call
"syn match uruzRoot "\<[a-zA-Z][_$a-zA-Z0-9]*\."me=e-1
"syn match uruzMethodCall "\.[a-z][_$a-zA-Z0-9]*"ms=s+1
"
"" type declarations in val/var/def
"syn match uruzType ":\s*\(=>\s*\)\?[._$a-zA-Z0-9]\+\(\[[^]]*\]\+\)\?\(\s*\(<:\|>:\|#\|=>\)\s*[._$a-zA-Z0-9]\+\(\[[^]]*\]\+\)*\)*" contained
syn match uruzType ":\s*" nextgroup=uruzNoType,ocamlMatchType,ocamlKeyType skipwhite
syn match uruzNoType "[~]" contained nextgroup=ocamlMatchCode skipwhite
syn match uruzOp "[*?+|=;()]" nextgroup=ocamlMatchCode,uruzType skipwhite
syn match uruzName "#[ \n\r\ta-zA-Z0-9_]*" nextgroup=ocamlMatchCode,uruzType skipwhite
syn match uruzEqOp ":=" nextgroup=ocamlMatchCode skipwhite
"
"" comments
syn match uruzTodo "[tT][oO][dD][oO]" contained
syn match uruzLineComment "//.*" contains=uruzTodo
syn region uruzComment start="/\*" end="\*/" contains=uruzTodo
"syn case ignore
"syn include @uruzHtml syntax/html.vim
"unlet b:current_syntax
"syn case match
"syn region uruzDocComment start="/\*\*" end="\*/" contains=uruzDocTags,uruzTodo,@uruzHtml keepend
"syn region uruzDocTags start="{@\(link\|linkplain\|inherit[Dd]oc\|doc[rR]oot\|value\)" end="}" contained
"syn match uruzDocTags "@[a-z]\+" contained
"
syn match uruzEmptyString "\"\""
"
"" multi-line string literals
"syn region uruzMultiLineString start="\"\"\"" end="\"\"\"" contains=uruzUnicode
"syn match uruzUnicode "\\u[0-9a-fA-F]\{4}" contained
"
"" string literals with escapes
syn region uruzCharset start="\[[^]]" skip="\\\"" end="\]" contains=uruzStringEscape
syn region uruzString start="\"[^"]" skip="\\\"" end="\"" contains=uruzStringEscape
syn match uruzStringEscape "\\[0-9]\{3}" contained
syn match uruzStringEscape "\\[nrfvb\\\"]" contained
"
"" symbol and character literals
"syn match uruzSymbol "'[_a-zA-Z0-9][_a-zA-Z0-9]*\>"
syn match uruzChar "'[^'\\]'\|'\\.'\|'\\u[0-9a-fA-F]\{4}'"
"
"" number literals
syn match uruzNumber "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match uruzNumber "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
syn match uruzNumber "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
syn match uruzNumber "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
"
"" xml literals
"syn match uruzXmlTag "<[a-zA-Z]\_[^>]*/>" contains=uruzXmlQuote,uruzXmlEscape,uruzXmlString
"syn region uruzXmlString start="\"" end="\"" contained
"syn match uruzXmlStart "<[a-zA-Z]\_[^>]*>" contained contains=uruzXmlQuote,uruzXmlEscape,uruzXmlString
"syn region uruzXml start="<\([a-zA-Z]\_[^>]*\_[^/]\|[a-zA-Z]\)>" matchgroup=uruzXmlStart end="</\_[^>]\+>" contains=uruzXmlEscape,uruzXmlQuote,uruzXml,uruzXmlStart,uruzXmlComment
"syn region uruzXmlEscape matchgroup=uruzXmlEscapeSpecial start="{" matchgroup=uruzXmlEscapeSpecial end="}" contained contains=TOP
"syn match uruzXmlQuote "&[^;]\+;" contained
"syn match uruzXmlComment "<!--\_[^>]*-->" contained
"
"syn sync fromstart
"
"" map groups to standard groups
hi link uruzKeyword Keyword
hi link uruzAnnotName SpecialComment
hi link uruzOp Keyword
hi link uruzEqOp SpecialComment
"hi link uruzPackage Include
"hi link uruzImport Include
hi link uruzBoolean Boolean
"hi link uruzOperator Normal
hi link uruzNumber Number
hi link uruzEmptyString String
hi link uruzString String
hi link uruzCharset String
hi link uruzChar String
hi link uruzMultiLineString String
hi link uruzStringEscape Special
"hi link uruzSymbol Special
"hi link uruzUnicode Special
hi link uruzComment Comment
hi link uruzLineComment Comment
"hi link uruzDocComment Comment
"hi link uruzDocTags Special
hi link uruzTodo Todo
hi link uruzType SpecialComment
hi link uruzNoType Type
hi link uruzName SpecialComment
"hi link uruzTypeSpecializer uruzType
"hi link uruzXml String
"hi link uruzXmlTag Include
"hi link uruzXmlString String
"hi link uruzXmlStart Include
"hi link uruzXmlEscape Normal
"hi link uruzXmlEscapeSpecial Special
"hi link uruzXmlQuote Special
"hi link uruzXmlComment Comment
hi link uruzDef Keyword
"hi link uruzVar Keyword
"hi link uruzVal Keyword
"hi link uruzClass Keyword
"hi link uruzObject Keyword
"hi link uruzTrait Keyword
hi link uruzDefName Function
"hi link uruzDefSpecializer Function
"hi link uruzClassName Special
"hi link uruzClassSpecializer Special
"hi link uruzConstructor Special
"hi link uruzConstructorSpecializer uruzConstructor

let b:current_syntax = "gra"

" you might like to put these lines in your .vimrc
"
" customize colors a little bit (should be a different file)
" hi uruzNew gui=underline
" hi uruzMethodCall gui=italic
" hi uruzValName gui=underline
" hi uruzVarName gui=underline
