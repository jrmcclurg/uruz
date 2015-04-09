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
  \ contained nextgroup=pggType,ocamlMatchCode skipwhite
  \ contains=@'.group
  execute 'syntax region ocamlMatch'.a:thename2.'
  \ matchgroup='.a:textSnipHl.'
  \ start="'.a:start2.'" end="'.a:end2.'"
  \ contained nextgroup=pggType,ocamlMatchCode skipwhite
  \ contains=@'.group
  execute 'syntax match ocamlKey'.a:thename2.'
  \ "'.a:pattern.'"
  \ contained nextgroup=pggType,ocamlMatchCode skipwhite
  \ contains=@'.group
endfunction

call TextEnableCodeSnip('ocaml', '{', '}', '(', ')', '[a-zA-Z0-9_~.]\+', 'SpecialComment', 'Code', 'Type')
"call TextEnableCodeSnip('ocaml', '(', ')', 'SpecialComment', 'Type')
"call TextEnableCodeSnip2('ocaml', '[a-zA-Z0-9_~.]\+', 'SpecialComment', 'Type')

" most keywords
syn keyword pggKeyword property keyword token eof nextgroup=pggType,ocamlMatchCode skipwhite
"syn match pggKeyword "=>"
"syn match pggKeyword "<-"
"syn match pggKeyword "\<_\>"

"syn match pggOperator ":\{2,\}" "this is not a type
"
"" package and import statements
"syn keyword pggPackage package nextgroup=pggFqn skipwhite
"syn keyword pggImport import nextgroup=pggFqn skipwhite
"syn match pggFqn "\<[._$a-zA-Z0-9,]*" contained nextgroup=pggFqnSet
"syn region pggFqnSet start="{" end="}" contained
"
"" boolean literals
syn keyword pggBoolean true false nextgroup=pggType,ocamlMatchCode skipwhite
"
"" definitions
syn keyword pggDef parser lexer ast nextgroup=pggDefName skipwhite
"syn keyword pggVal val nextgroup=pggValName skipwhite
"syn keyword pggVar var nextgroup=pggVarName skipwhite
"syn keyword pggClass class nextgroup=pggClassName skipwhite
"syn keyword pggObject object nextgroup=pggClassName skipwhite
"syn keyword pggTrait trait nextgroup=pggClassName skipwhite
syn match pggDefName "[a-zA-Z0-9_~]\+" nextgroup=ocamlMatchCode,pggType,pggEqOp skipwhite
syn match pggAnnotName "@[a-zA-Z0-9_]\+" nextgroup=ocamlMatchCode skipwhite
"syn match pggValName "[^ =:;([]\+" contained
"syn match pggVarName "[^ =:;([]\+" contained 
"syn match pggClassName "[^ =:;(\[]\+" contained nextgroup=pggClassSpecializer skipwhite
"syn region pggDefSpecializer start="\[" end="\]" contained contains=pggDefSpecializer
"syn region pggClassSpecializer start="\[" end="\]" contained contains=pggClassSpecializer
"
"" type constructor (actually anything with an uppercase letter)
"syn match pggConstructor "\<[A-Z][_$a-zA-Z0-9]*\>" nextgroup=pggConstructorSpecializer
"syn region pggConstructorSpecializer start="\[" end="\]" contained contains=pggConstructorSpecializer
"
"" method call
"syn match pggRoot "\<[a-zA-Z][_$a-zA-Z0-9]*\."me=e-1
"syn match pggMethodCall "\.[a-z][_$a-zA-Z0-9]*"ms=s+1
"
"" type declarations in val/var/def
"syn match pggType ":\s*\(=>\s*\)\?[._$a-zA-Z0-9]\+\(\[[^]]*\]\+\)\?\(\s*\(<:\|>:\|#\|=>\)\s*[._$a-zA-Z0-9]\+\(\[[^]]*\]\+\)*\)*" contained
syn match pggType ":\s*" nextgroup=pggNoType,ocamlMatchType,ocamlKeyType skipwhite
syn match pggNoType "[~]" contained nextgroup=ocamlMatchCode skipwhite
syn match pggOp "[*?+|=;()]" nextgroup=ocamlMatchCode,pggType skipwhite
syn match pggName "#[ \n\r\ta-zA-Z0-9_]*" nextgroup=ocamlMatchCode,pggType skipwhite
syn match pggEqOp ":=" nextgroup=ocamlMatchCode skipwhite
"
"" comments
syn match pggTodo "[tT][oO][dD][oO]" contained
syn match pggLineComment "//.*" contains=pggTodo
syn region pggComment start="/\*" end="\*/" contains=pggTodo
"syn case ignore
"syn include @pggHtml syntax/html.vim
"unlet b:current_syntax
"syn case match
"syn region pggDocComment start="/\*\*" end="\*/" contains=pggDocTags,pggTodo,@pggHtml keepend
"syn region pggDocTags start="{@\(link\|linkplain\|inherit[Dd]oc\|doc[rR]oot\|value\)" end="}" contained
"syn match pggDocTags "@[a-z]\+" contained
"
syn match pggEmptyString "\"\""
"
"" multi-line string literals
"syn region pggMultiLineString start="\"\"\"" end="\"\"\"" contains=pggUnicode
"syn match pggUnicode "\\u[0-9a-fA-F]\{4}" contained
"
"" string literals with escapes
syn region pggCharset start="\[[^]]" skip="\\\"" end="\]" contains=pggStringEscape
syn region pggString start="\"[^"]" skip="\\\"" end="\"" contains=pggStringEscape
syn match pggStringEscape "\\[0-9]\{3}" contained
syn match pggStringEscape "\\[nrfvb\\\"]" contained
"
"" symbol and character literals
"syn match pggSymbol "'[_a-zA-Z0-9][_a-zA-Z0-9]*\>"
syn match pggChar "'[^'\\]'\|'\\.'\|'\\u[0-9a-fA-F]\{4}'"
"
"" number literals
syn match pggNumber "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match pggNumber "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
syn match pggNumber "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
syn match pggNumber "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
"
"" xml literals
"syn match pggXmlTag "<[a-zA-Z]\_[^>]*/>" contains=pggXmlQuote,pggXmlEscape,pggXmlString
"syn region pggXmlString start="\"" end="\"" contained
"syn match pggXmlStart "<[a-zA-Z]\_[^>]*>" contained contains=pggXmlQuote,pggXmlEscape,pggXmlString
"syn region pggXml start="<\([a-zA-Z]\_[^>]*\_[^/]\|[a-zA-Z]\)>" matchgroup=pggXmlStart end="</\_[^>]\+>" contains=pggXmlEscape,pggXmlQuote,pggXml,pggXmlStart,pggXmlComment
"syn region pggXmlEscape matchgroup=pggXmlEscapeSpecial start="{" matchgroup=pggXmlEscapeSpecial end="}" contained contains=TOP
"syn match pggXmlQuote "&[^;]\+;" contained
"syn match pggXmlComment "<!--\_[^>]*-->" contained
"
"syn sync fromstart
"
"" map groups to standard groups
hi link pggKeyword Keyword
hi link pggAnnotName SpecialComment
hi link pggOp Keyword
hi link pggEqOp SpecialComment
"hi link pggPackage Include
"hi link pggImport Include
hi link pggBoolean Boolean
"hi link pggOperator Normal
hi link pggNumber Number
hi link pggEmptyString String
hi link pggString String
hi link pggCharset String
hi link pggChar String
hi link pggMultiLineString String
hi link pggStringEscape Special
"hi link pggSymbol Special
"hi link pggUnicode Special
hi link pggComment Comment
hi link pggLineComment Comment
"hi link pggDocComment Comment
"hi link pggDocTags Special
hi link pggTodo Todo
hi link pggType SpecialComment
hi link pggNoType Type
hi link pggName SpecialComment
"hi link pggTypeSpecializer pggType
"hi link pggXml String
"hi link pggXmlTag Include
"hi link pggXmlString String
"hi link pggXmlStart Include
"hi link pggXmlEscape Normal
"hi link pggXmlEscapeSpecial Special
"hi link pggXmlQuote Special
"hi link pggXmlComment Comment
hi link pggDef Keyword
"hi link pggVar Keyword
"hi link pggVal Keyword
"hi link pggClass Keyword
"hi link pggObject Keyword
"hi link pggTrait Keyword
hi link pggDefName Function
"hi link pggDefSpecializer Function
"hi link pggClassName Special
"hi link pggClassSpecializer Special
"hi link pggConstructor Special
"hi link pggConstructorSpecializer pggConstructor

let b:current_syntax = "gra"

" you might like to put these lines in your .vimrc
"
" customize colors a little bit (should be a different file)
" hi pggNew gui=underline
" hi pggMethodCall gui=italic
" hi pggValName gui=underline
" hi pggVarName gui=underline
