(()=>{'use strict';
const STORE='chordoku.save.v1',BEST='chordoku.best.v1',WAKE_PREF='chordoku.keepScreenAwake.v1';
const ROOTS=[['C',0],['Db',1],['D',2],['Eb',3],['E',4],['F',5],['Gb',6],['G',7],['Ab',8],['A',9],['Bb',10],['B',11]];
const SUDOKU_LEVELS=[
 {id:'easy',label:'Лёгкая',range:[40,44]},
 {id:'medium',label:'Средняя',range:[34,38]},
 {id:'hard',label:'Сложная',range:[29,32]},
 {id:'terrible',label:'Страшная',range:[24,27]}
];
const CHORD_LEVELS=SUDOKU_LEVELS;
const CHORD_COLORS=['#f28b82','#ffb86b','#f0d36d','#8ecf82','#63c6c2','#7eacf2','#9990e8','#c28bdf','#e68db8'];
const QUALITIES=[
 {id:'major',suffix:'',tier:0,intervals:[0,4,7],kind:'major'},
 {id:'minor',suffix:'m',tier:0,intervals:[0,3,7],kind:'minor'},
 {id:'diminished',suffix:'dim',tier:1,intervals:[0,3,6],kind:'other'},
 {id:'augmented',suffix:'aug',tier:1,intervals:[0,4,8],kind:'other'},
 {id:'dominant7',suffix:'7',tier:2,intervals:[0,4,7,10],kind:'seventh'},
 {id:'major7',suffix:'maj7',tier:2,intervals:[0,4,7,11],kind:'seventh'},
 {id:'minor7',suffix:'m7',tier:2,intervals:[0,3,7,10],kind:'seventh'},
 {id:'halfDim7',suffix:'m7♭5',tier:2,intervals:[0,3,6,10],kind:'seventh'},
 {id:'dim7',suffix:'dim7',tier:2,intervals:[0,3,6,9],kind:'seventh'},
 {id:'dominant9',suffix:'9',tier:3,intervals:[0,4,7,10,14],kind:'ninth'},
 {id:'major9',suffix:'maj9',tier:3,intervals:[0,4,7,11,14],kind:'ninth'},
 {id:'minor9',suffix:'m9',tier:3,intervals:[0,3,7,10,14],kind:'ninth'}
];
const SOLVED=['534678912','672195348','198342567','859761423','426853791','713924856','961537284','287419635','345286179'].map(r=>r.split('').map(Number));
const PUZZLE=['530070000','600195000','098000060','800060003','400803001','700020006','060000280','000419005','000080079'].map(r=>r.split('').map(Number));
const NAV=[['До',0],['До♯',1],['Ре',2],['Ре♯',3],['Ми',4],['Фа',5],['Фа♯',6],['Соль',7],['Соль♯',8]],CHORD_WINDOW_MS=220,TAP_WINDOW_MS=520;
let game,midi=null,midiInputs=new Map(),midiRequest=null,midiError='',wakeLock=null,wakeRequest=null,wakeEnabled=true,wakeError='',held=new Set(),pedal=false,noteBatch=[],noteTimer=null,pendingTap=null,tapTimer=null,notification=null,overlaySaved=false,winModalDismissed=false,timerNode=null;
const $=s=>document.querySelector(s),cloneGrid=g=>g.map(r=>r.slice()),shuffle=a=>{const b=[...a];for(let i=b.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[b[i],b[j]]=[b[j],b[i]]}return b},randomBetween=(min,max)=>min+Math.floor(Math.random()*(max-min+1));
function levelIndex(level){const i=SUDOKU_LEVELS.findIndex(x=>x.id===level);return i<0?0:i}
function groupOrder(){return shuffle([0,1,2]).flatMap(group=>shuffle([0,1,2]).map(part=>group*3+part))}
function randomizedBase(){
 const rows=groupOrder(),cols=groupOrder();
 let solution=rows.map(r=>cols.map(c=>SOLVED[r][c])),puzzle=rows.map(r=>cols.map(c=>PUZZLE[r][c]));
 if(Math.random()<.5){solution=solution[0].map((_,c)=>solution.map(r=>r[c]));puzzle=puzzle[0].map((_,c)=>puzzle.map(r=>r[c]))}
 const digits=shuffle([1,2,3,4,5,6,7,8,9]);
 solution=solution.map(r=>r.map(v=>digits[v-1]));puzzle=puzzle.map(r=>r.map(v=>v?digits[v-1]:0));
 return {solution,puzzle}
}
function bitCount(n){let c=0;while(n){n&=n-1;c++}return c}
function countSolutions(source,limit=2){
 const grid=cloneGrid(source),rows=Array(9).fill(0),cols=Array(9).fill(0),boxes=Array(9).fill(0),full=0x3fe;
 for(let r=0;r<9;r++)for(let c=0;c<9;c++){const v=grid[r][c];if(!v)continue;const bit=1<<v,b=(r/3|0)*3+(c/3|0);if((rows[r]&bit)||(cols[c]&bit)||(boxes[b]&bit))return 0;rows[r]|=bit;cols[c]|=bit;boxes[b]|=bit}
 function solve(){
  let bestR=-1,bestC=-1,bestMask=0,bestCount=10;
  scan:for(let r=0;r<9;r++)for(let c=0;c<9;c++){if(grid[r][c])continue;const b=(r/3|0)*3+(c/3|0),mask=full&~(rows[r]|cols[c]|boxes[b]),n=bitCount(mask);if(n===0)return 0;if(n<bestCount){bestR=r;bestC=c;bestMask=mask;bestCount=n;if(n===1)break scan}}
  if(bestR<0)return 1;
  const b=(bestR/3|0)*3+(bestC/3|0);let found=0,mask=bestMask;
  while(mask){const bit=mask&-mask;mask-=bit;const value=31-Math.clz32(bit);grid[bestR][bestC]=value;rows[bestR]|=bit;cols[bestC]|=bit;boxes[b]|=bit;found+=solve();rows[bestR]^=bit;cols[bestC]^=bit;boxes[b]^=bit;grid[bestR][bestC]=0;if(found>=limit)return found}
  return found
 }
 return solve()
}
function clueCount(grid){return grid.flat().filter(Boolean).length}
function puzzleAtDifficulty(basePuzzle,baseSolution,level){
 const range=(SUDOKU_LEVELS.find(x=>x.id===level)||SUDOKU_LEVELS[0]).range,target=randomBetween(range[0],range[1]),start=cloneGrid(basePuzzle),startCount=clueCount(start);
 if(startCount<target){const cells=shuffle(Array.from({length:81},(_,i)=>i).filter(i=>!start[i/9|0][i%9]));for(const i of cells){if(clueCount(start)>=target)break;const r=i/9|0,c=i%9;start[r][c]=baseSolution[r][c]}return start}
 if(startCount===target)return start;
 let best=cloneGrid(start),bestCount=startCount;
 for(let attempt=0;attempt<160;attempt++){
  const trial=cloneGrid(start);let count=startCount;
  for(const i of shuffle(Array.from({length:81},(_,n)=>n))){
   if(count<=target)break;const r=i/9|0,c=i%9,value=trial[r][c];if(!value)continue;trial[r][c]=0;
   if(countSolutions(trial,2)===1){count--;if(count<bestCount){best=cloneGrid(trial);bestCount=count}}else trial[r][c]=value
  }
  if(count===target)return trial
 }
 return best
}
function chordPool(level){
 const maxTier=levelIndex(level),unique=new Map();
 for(const [root,pc] of ROOTS)for(const q of QUALITIES){if(q.tier>maxTier)continue;const pcs=q.intervals.map(i=>(pc+i)%12),key=[...pcs].sort((a,b)=>a-b).join('-');if(unique.has(key))continue;unique.set(key,{root,pc,quality:q.id,tier:q.tier,kind:q.kind,minor:q.id==='minor'||q.id==='minor7'||q.id==='minor9',label:root+q.suffix,pcs,intervals:q.intervals.slice(),notes:q.intervals.map(i=>60+pc+i)})}
 return [...unique.values()]
}
function randomChords(level='easy'){
 const pool=chordPool(level),tier=levelIndex(level),picked=[];
 function take(test){const options=shuffle(pool.filter(c=>test(c)&&!picked.some(p=>p.pcs.length===c.pcs.length&&p.pcs.every(v=>c.pcs.includes(v)))));if(options.length)picked.push(options[0])}
 take(c=>c.quality==='major');take(c=>c.quality==='minor');if(tier>0)take(c=>c.tier===tier);
 for(const chord of shuffle(pool)){if(picked.length>=9)break;if(!picked.some(p=>p.pcs.length===chord.pcs.length&&p.pcs.every(v=>chord.pcs.includes(v))))picked.push(chord)}
 return picked.slice(0,9).map(c=>({...c,pcs:c.pcs.slice(),intervals:c.intervals.slice(),notes:c.notes.slice()}))
}
function fresh(sudokuLevel='easy',chordLevel='easy'){
 const base=randomizedBase(),puzzleDigits=puzzleAtDifficulty(base.puzzle,base.solution,sudokuLevel),chords=randomChords(chordLevel),map=shuffle([1,2,3,4,5,6,7,8,9]);
 const solution=base.solution.map(r=>r.map(v=>map[v-1])),puzzle=puzzleDigits.map(r=>r.map(v=>v?map[v-1]:0));
 return {puzzle,solution,values:cloneGrid(puzzle),candidates:Array.from({length:9},()=>Array.from({length:9},()=>[])),chords,selected:40,block:4,strict:false,sudokuLevel,chordLevel,started:Date.now(),elapsed:0,timerPaused:false,errors:0,hints:0,undos:0,redos:0,plays:0,history:[],redoStack:[],wrong:[],immediateWrong:[],checked:false,won:false}
}
function levelForClues(grid){const n=clueCount(grid);return n>=39?'easy':n>=33?'medium':n>=28?'hard':'terrible'}
function ensureSavedGame(x){
 if(!Array.isArray(x.chords)||x.chords.length!==9)x.chords=randomChords(x.chordLevel||'easy');
 if(!SUDOKU_LEVELS.some(l=>l.id===x.sudokuLevel))x.sudokuLevel=levelForClues(x.puzzle||[]);
 if(!SUDOKU_LEVELS.some(l=>l.id===x.chordLevel))x.chordLevel='easy';
 if(!Array.isArray(x.redoStack))x.redoStack=[];
 if(!Array.isArray(x.history))x.history=[];else x.history=x.history.map(s=>{try{return typeof s==='string'?JSON.parse(s):s}catch{return null}}).filter(s=>s?.values?.length===9&&s?.candidates?.length===9);
 if(!Array.isArray(x.candidates))x.candidates=Array.from({length:9},()=>Array.from({length:9},()=>[]));
 if(!Array.isArray(x.immediateWrong))x.immediateWrong=[];
 if(!Number.isInteger(x.block))x.block=Math.floor(x.selected/27)*3+Math.floor((x.selected%9)/3);
 return x
}
function fmt(s){s=Math.max(0,Math.floor(s));return String(s/3600|0).padStart(2,'0')+':'+String(s/60%60|0).padStart(2,'0')+':'+String(s%60).padStart(2,'0')}
function duration(){return game.elapsed+(!game.timerPaused?Math.floor((Date.now()-game.started)/1000):0)}
function chordName(value){return game?.chords?.[value-1]?.label||'—'}
function sudokuName(id){return (SUDOKU_LEVELS.find(x=>x.id===id)||SUDOKU_LEVELS[0]).label}
function save(){try{if(game&&!game.won)localStorage.setItem(STORE,JSON.stringify(game))}catch{}}
function load(){try{const x=JSON.parse(localStorage.getItem(STORE));if(x&&x.values?.length===9&&x.solution?.length===9)return ensureSavedGame(x)}catch{}return null}
function recognized(notes){const pcs=[...new Set(notes.map(n=>n%12))];if(pcs.length<3)return 0;return game.chords.findIndex(c=>c.pcs.length===pcs.length&&c.pcs.every(pc=>pcs.includes(pc)))+1}
function chordCounts(){return game.values.flat().reduce((counts,v)=>{if(v)counts[v-1]++;return counts},Array(9).fill(0))}
function render(){
 if(!game)return;
 const filled=game.values.flat().filter(Boolean).length,counts=chordCounts(),selected=game.selected,sr=selected/9|0,sc=selected%9,recognizedValue=held.size?recognized([...held]):0;
 const activeBlock=(sr/3|0)*3+(sc/3|0);
 const board=Array.from({length:9},(_,block)=>{
  const br=(block/3|0)*3,bc=block%3*3,cells=[];
  for(let rr=0;rr<3;rr++)for(let cc=0;cc<3;cc++){
   const r=br+rr,c=bc+cc,value=game.values[r][c],i=r*9+c,given=!!game.puzzle[r][c],selectedCell=i===selected,related=r===sr||c===sc||((r/3|0)===(sr/3|0)&&(c/3|0)===(sc/3|0)),local=rr*3+cc,cellColor=value?(counts[value-1]>=9?'#929292':CHORD_COLORS[value-1]):'';
   cells.push('<button class="cell '+(given?'given ':'')+(selectedCell?'selected ':'')+(!selectedCell&&related?'related ':'')+((game.wrong.includes(i)||(game.immediateWrong||[]).includes(i))?'error':'')+'" data-i="'+i+'"'+(value?' data-value="'+value+'" style="--chord-color:'+cellColor+';--chord-bg:'+cellColor+'28;--chord-selected-bg:'+cellColor+'40"':'')+'>'+(value?'<span class="value'+(chordName(value).length>3?' long-label':'')+'">'+chordName(value)+'</span>':'<span class="pencil">'+Array.from({length:9},(_,k)=>{const name=game.candidates[r][c].includes(k+1)?chordName(k+1):'',candidateColor=counts[k]>=9?'#929292':CHORD_COLORS[k];return '<span class="candidate-color'+(name.length>3?' long-label':'')+'" style="--chord-color:'+candidateColor+'">'+name+'</span>'}).join('')+'</span>')+'<span class="cell-key">'+(local+1)+'</span></button>')
  }
  return '<div class="board-block"><span class="block-label'+(block===activeBlock?' active':'')+'">'+NAV[block][0]+'</span>'+cells.join('')+'</div>'
 }).join('');
 const chordRows=game.chords.map((chord,i)=>{const completed=counts[i]>=9,color=completed?'#929292':CHORD_COLORS[i],remaining=Math.max(0,9-counts[i]);return '<button class="reference-chord'+(completed?' completed':'')+'" data-chord="'+(i+1)+'" style="--chord-color:'+color+';--chord-bg:'+color+'18"><span class="reference-index">'+(i+1)+'</span><strong>'+chord.label+'</strong><span class="reference-count">'+remaining+'</span></button>'}).join('');
 const notes=[...held].sort((a,b)=>a-b).map(midiName).join(' · ');
 const keyNotes=Array.from({length:88},(_,i)=>i+21).map(n=>{const pc=n%12,black=[1,3,6,8,10].includes(pc),lit=held.has(n);return '<i class="piano-key '+(black?'black-key':'white-key')+(lit?' lit':'')+'" data-note="'+n+'" style="left:'+(black?whiteKeyIndex(n)*100/52-100/52*.32:whiteKeyIndex(n)*100/52)+'%" title="'+midiName(n)+'"></i>'}).join('');
 const logo='<img class="brand-logo" src="logo.svg" alt="Chordoku">';
 $('#app').innerHTML='<main class="shell"><header class="controlbar">'+logo+'<div class="stat timer-stat"><label>Время</label><strong id="gameTimer">'+fmt(duration())+'</strong></div><button class="btn small timer-toggle" id="timerToggle" title="'+(game.timerPaused?'Возобновить таймер':'Пауза таймера')+'">'+(game.timerPaused?'▶':'Ⅱ')+'</button><div class="stat progress-stat"><label>Заполнено</label><strong>'+filled+' / 81</strong><div class="progress"><i style="width:'+filled/81*100+'%"></i></div></div><button class="btn small" id="undo">↶ Undo</button><button class="btn small" id="redo">↷ Redo</button><button class="btn small" id="clear">⌫ Clear</button><div class="hint-anchor"><button class="btn small" id="hint" aria-expanded="false" aria-controls="hintPopover">✦ Подсказка</button><div class="hint-popover hidden" id="hintPopover" role="status" aria-live="polite"></div></div><button class="btn small" id="new">Новая партия</button><button class="btn small" id="settings">⚙</button><button class="btn small primary" id="check">Проверить</button></header><section class="board-stage"><aside class="guide-panel"><h2>Управление</h2><h3>Навигация</h3><p class="guide-caption">Ноты До–Соль♯ без&nbsp;педали выбирают блоки 1–9.</p><div class="guide-list">'+NAV.map(([name],i)=>'<div><span>'+name+'</span><b>'+(i+1)+'</b></div>').join('')+'</div><p class="guide-instructions">Удерживай sustain-педаль и нажми ту же ноту, чтобы выбрать одну из&nbsp;9 клеток внутри&nbsp;блока.</p><h3>Как играть</h3><div class="guide-steps"><div class="guide-step"><b>1</b><div><strong>Кандидаты</strong><span>Сыграй аккорд без&nbsp;педали.</span></div></div><div class="guide-step"><b>2</b><div><strong>Финальный ответ</strong><span>Удерживай педаль и сыграй аккорд.</span></div></div><div class="guide-step"><b>3</b><div><strong>Проверка</strong><span>Заполни поле и нажми «Проверить».</span></div></div></div><p class="guide-rule">В&nbsp;каждой строке, столбце и блоке должны быть все девять аккордов без&nbsp;повторов.</p><div class="guide-shortcuts"><span>До ×3</span><b>Undo</b><span>Ре ×3</span><b>Redo</b><span>Соль ×3</span><b>Очистить</b></div></aside><div class="board-wrap"><div class="board">'+board+'</div></div><aside class="reference-panel"><h2>Аккорды партии</h2><p class="guide-caption">Осталось заполнить до 9</p><div class="reference-list">'+chordRows+'</div></aside></section><section class="piano-area"><div class="live-chord"><strong id="liveChord">'+(recognizedValue?game.chords[recognizedValue-1].label:(held.size?'Аккорд не распознан':'—'))+'</strong><span id="liveNotes">'+(notes||'Сыграй аккорд')+'</span></div><div class="input-row"><div class="input-status"><span class="pedal '+(pedal?'on':'')+'"></span><span>'+(pedal?'Педаль нажата':'Педаль отпущена')+'</span><span class="midi-status" id="midiStatus">'+midiStatusText()+'</span></div><button id="connect" class="btn small">'+(midi?'Переподключить MIDI':'Подключить MIDI')+'</button></div><div class="piano">'+keyNotes+'</div><div class="piano-label">Клавиатура · 88 клавиш</div></section></main><div id="modal"></div>';
 timerNode=$('#gameTimer');$('#timerToggle').onclick=toggleTimer;$('#undo').onclick=undo;$('#redo').onclick=redo;$('#clear').onclick=clearCell;$('#hint').onclick=hint;$('#new').onclick=confirmNew;$('#settings').onclick=settings;$('#check').onclick=check;$('#connect').onclick=connect;
 document.querySelectorAll('.cell').forEach(b=>b.onclick=()=>{game.selected=+b.dataset.i;game.block=(game.selected/27|0)*3+(game.selected%9/3|0);game.wrong=[];save();render()});
 document.querySelectorAll('[data-chord]').forEach(b=>{b.onclick=()=>commit(+b.dataset.chord);b.onmouseenter=()=>previewChord(+b.dataset.chord,true);b.onmouseleave=()=>previewChord(+b.dataset.chord,false)});
 document.onkeydown=keyHandler;renderModal();tickTimer()
}
function whiteKeyIndex(n){let count=0;for(let k=21;k<n;k++)if(![1,3,6,8,10].includes(k%12))count++;return count}
function midiName(n){const names=['C','Db','D','Eb','E','F','Gb','G','Ab','A','Bb','B'];return names[n%12]+(Math.floor(n/12)-1)}
function midiBrowserMessage(){return 'Web MIDI недоступен в этом браузере. Открой сайт в Chrome или Яндекс Браузере.'}
function midiStatusText(){if(midiError)return midiError;if(!window.isSecureContext)return 'Для MIDI нужно открыть сайт по HTTPS.';if(!navigator.requestMIDIAccess)return midiBrowserMessage();if(!midi)return 'MIDI не подключена';return midi.inputs.size?'Подключена: '+[...midi.inputs.values()].map(x=>x.name||'MIDI-клавиатура').join(', '):'Доступ разрешён · клавиатура не найдена'}
function previewChord(index,on){
 const chord=game.chords[index-1];if(!chord)return;
 document.querySelectorAll('.piano-key').forEach(key=>{if(chord.notes.includes(+key.dataset.note))key.classList.toggle('preview-lit',on)});
 document.querySelectorAll('.cell[data-value]').forEach(cell=>cell.classList.toggle('chord-preview',on&&+cell.dataset.value===index))
}
function snapshot(){return {values:cloneGrid(game.values),candidates:game.candidates.map(r=>r.map(a=>a.slice())),immediateWrong:(game.immediateWrong||[]).slice()}}
function pushHistory(){game.history.push(snapshot());game.redoStack=[]}
function restore(s){game.values=cloneGrid(s.values);game.candidates=s.candidates.map(r=>r.map(a=>a.slice()));game.immediateWrong=Array.isArray(s.immediateWrong)?s.immediateWrong.slice():[];game.wrong=[];save();render()}
function commit(value){
 if(game.won)return;
 const i=game.selected,r=i/9|0,c=i%9,current=game.values[r][c],removing=pedal&&current===value;
 if(game.puzzle[r][c])return toast('Эта клетка задана в начале партии');
 if(!pedal&&current)return toast('В клетке уже есть ответ. Удерживай педаль и повтори его, чтобы удалить.');
 const invalidAnswer=pedal&&game.strict&&!removing&&game.solution[r][c]!==value;
 pushHistory();game.plays++;game.wrong=[];
 if(pedal){
  if(removing){game.values[r][c]=0;game.candidates[r][c]=[];game.immediateWrong=game.immediateWrong.filter(x=>x!==i);toast('Аккорд удалён из клетки')}
  else{game.values[r][c]=value;game.candidates[r][c]=[];game.immediateWrong=game.immediateWrong.filter(x=>x!==i);if(invalidAnswer){game.immediateWrong.push(i);game.errors++;toast('Неверный ответ оставлен в клетке и отмечен красным')}for(let n=0;n<81;n++){const rr=n/9|0,cc=n%9;if(n!==i&&(rr===r||cc===c||((rr/3|0)===(r/3|0)&&(cc/3|0)===(c/3|0))))game.candidates[rr][cc]=game.candidates[rr][cc].filter(x=>x!==value)}}
 }else{const a=game.candidates[r][c];game.candidates[r][c]=a.includes(value)?a.filter(x=>x!==value):[...a,value].sort((a,b)=>a-b)}
 save();render()
}
function undo(){if(!game.history.length)return toast('Нечего отменять');game.redoStack.push(snapshot());game.undos++;restore(game.history.pop())}
function redo(){if(!game.redoStack.length)return toast('Нечего повторять');game.history.push(snapshot());game.redos++;restore(game.redoStack.pop())}
function clearCell(){const i=game.selected,r=i/9|0,c=i%9;if(game.puzzle[r][c])return toast('Исходную клетку нельзя очистить');if(!game.values[r][c]&&!game.candidates[r][c].length)return;pushHistory();game.values[r][c]=0;game.candidates[r][c]=[];game.immediateWrong=game.immediateWrong.filter(x=>x!==i);game.wrong=[];save();render()}
function candidatesFor(values,r,c){const used=new Set();for(let i=0;i<9;i++){if(values[r][i])used.add(values[r][i]);if(values[i][c])used.add(values[i][c])}const br=(r/3|0)*3,bc=(c/3|0)*3;for(let rr=br;rr<br+3;rr++)for(let cc=bc;cc<bc+3;cc++)if(values[rr][cc])used.add(values[rr][cc]);return [1,2,3,4,5,6,7,8,9].filter(v=>!used.has(v))}
function sudokuUnits(){
 const units=[];for(let r=0;r<9;r++)units.push({label:'строке '+(r+1),cells:Array.from({length:9},(_,c)=>r*9+c)});
 for(let c=0;c<9;c++)units.push({label:'столбце '+(c+1),cells:Array.from({length:9},(_,r)=>r*9+c)});
 for(let b=0;b<9;b++){const br=(b/3|0)*3,bc=b%3*3,cells=[];for(let r=br;r<br+3;r++)for(let c=bc;c<bc+3;c++)cells.push(r*9+c);units.push({label:'блоке '+NAV[b][0],cells})}
 return units
}
function deliverHint(message){game.hints++;save();const popover=$('#hintPopover');if(popover){popover.textContent='Подсказка: '+message;popover.classList.remove('hidden');$('#hint').setAttribute('aria-expanded','true')}}
function closeHintPopover(){const popover=$('#hintPopover');if(popover){popover.classList.add('hidden');$('#hint').setAttribute('aria-expanded','false')}}
function hint(){
 const popover=$('#hintPopover');if(popover&&!popover.classList.contains('hidden')){closeHintPopover();return}
 if(game.values.flat().every(Boolean))return deliverHint('поле заполнено — нажми «Проверить».');
 const wrong=game.values.some((row,r)=>row.some((v,c)=>v&&v!==game.solution[r][c]));
 if(wrong)return deliverHint('сначала проверь уже введённые ответы: один из них не подходит единственному решению этой партии.');
 const values=cloneGrid(game.values),possibilities=Array.from({length:9},()=>Array.from({length:9},()=>[])),empty=[];
 for(let r=0;r<9;r++)for(let c=0;c<9;c++)if(!values[r][c]){possibilities[r][c]=candidatesFor(values,r,c);empty.push({r,c,values:possibilities[r][c]})}
 const singles=empty.filter(x=>x.values.length===1).sort((a,b)=>a.values.length-b.values.length);
 if(singles.length){const x=singles[0];return deliverHint('следующий логичный ход — клетка в '+(x.r+1)+'-й строке и '+(x.c+1)+'-м столбце. После исключения аккордов из её строки, столбца и блока остаётся один вариант.')}
 const units=sudokuUnits();
 for(const unit of units){const blank=unit.cells.filter(i=>!values[i/9|0][i%9]);for(let value=1;value<=9;value++){if(unit.cells.some(i=>values[i/9|0][i%9]===value))continue;const spots=blank.filter(i=>possibilities[i/9|0][i%9].includes(value));if(spots.length===1){const r=spots[0]/9|0,c=spots[0]%9;return deliverHint('в '+unit.label+' один из недостающих аккордов может стоять только в одной клетке — проверь пересечение '+(r+1)+'-й строки и '+(c+1)+'-го столбца.')}}
 }
 for(const unit of units){const pairs=unit.cells.filter(i=>!values[i/9|0][i%9]&&possibilities[i/9|0][i%9].length===2);for(let a=0;a<pairs.length;a++)for(let b=a+1;b<pairs.length;b++){const x=pairs[a],y=pairs[b],xa=possibilities[x/9|0][x%9],ya=possibilities[y/9|0][y%9];if(xa[0]===ya[0]&&xa[1]===ya[1])return deliverHint('в '+unit.label+' две клетки ограничены одной и той же парой аккордов. Эта пара уже занята ими — исключи её из остальных клеток '+unit.label+'.')}}
 const target=empty.filter(x=>x.values.length).sort((a,b)=>a.values.length-b.values.length)[0];
 if(!target)return deliverHint('проверь текущие ответы: в поле нет допустимого варианта для одной из пустых клеток.');
 return deliverHint('начни с клетки в '+(target.r+1)+'-й строке и '+(target.c+1)+'-м столбце: в ней осталось '+target.values.length+' допустимых аккорда. Исключи те, что уже стоят в её строке, столбце и блоке.')
}
function check(){
 if(game.won)return;const empty=game.values.flat().filter(x=>!x).length;if(empty)return toast('Заполни ещё '+empty+' клеток перед проверкой');
 const wrong=[];game.values.forEach((row,r)=>row.forEach((v,c)=>{if(v!==game.solution[r][c])wrong.push(r*9+c)}));game.checked=true;game.wrong=wrong;
 if(wrong.length){const alreadyCounted=new Set(game.immediateWrong||[]);game.errors+=wrong.filter(i=>!alreadyCounted.has(i)).length;toast('Найдено ошибок: '+wrong.length+'. Исправь подсвеченные клетки и проверь снова.')}
 else{game.elapsed=duration();game.timerPaused=true;game.won=true;game.score=Math.max(0,10000-game.elapsed*2-game.errors*180-game.hints*250-game.undos*25);game.bestScore=Math.max(game.score,+(localStorage.getItem(BEST)||0));winModalDismissed=false;localStorage.removeItem(STORE);if(game.score>+(localStorage.getItem(BEST)||0))localStorage.setItem(BEST,game.score)}
 render()
}
function modal(content,extraClass=''){$('#modal').innerHTML='<div class="overlay"><div class="dialog card '+extraClass+'">'+content+'</div></div>'}
function levelSelect(id,label,levels,current){return '<label class="difficulty-row"><span>'+label+'</span><select id="'+id+'">'+levels.map(l=>'<option value="'+l.id+'"'+(l.id===current?' selected':'')+'>'+l.label+'</option>').join('')+'</select></label>'}
function startNewGame(sudokuLevel,chordLevel){overlaySaved=false;winModalDismissed=false;game=fresh(sudokuLevel,chordLevel);save();render()}
function openNewGameSettings(options={}){
 const initial=!!options.initial,fromSaved=!!options.fromSaved,fromWin=!!options.fromWin,canCancel=!initial&&!fromSaved;
 let copy=initial?'Выбери сложность судоку и аккордов. Раскладка каждой новой партии будет другой.':fromSaved?'Текущая партия и её прогресс будут заменены новой головоломкой.':fromWin?'Отличный результат! Выбери сложность следующей партии.':'Текущий прогресс будет заменён новой головоломкой.';
 let actions=(canCancel?'<button class="btn" id="cancelNew">'+(fromWin?'Назад':'Отмена')+'</button>':'')+'<button class="btn primary" id="yesNew">'+(initial?'Начать игру':fromWin?'Начать следующую партию':'Начать новую партию')+'</button>';
 modal('<h2>'+(initial?'Новая партия':'Сложность новой партии')+'</h2><p>'+copy+'</p>'+levelSelect('sudokuLevel','Сложность судоку',SUDOKU_LEVELS,game.sudokuLevel||'easy')+levelSelect('chordLevel','Сложность аккордов',CHORD_LEVELS,game.chordLevel||'easy')+'<div class="dialog-actions">'+actions+'</div>');
 if(canCancel)$('#cancelNew').onclick=()=>{if(fromSaved||fromWin)renderModal();else render()};
 $('#yesNew').onclick=()=>startNewGame($('#sudokuLevel').value,$('#chordLevel').value)
}
function renderModal(){
 if(game?.won){
  if(winModalDismissed){$('#modal').innerHTML='';return}
  const score=Number(game.score)||0,best=Number(game.bestScore)||score;
  const sparks=[];for(let burst=0;burst<2;burst++)for(let i=0;i<18;i++){const angle=(Math.PI*2*i/18)+(burst*.12),distance=35+(i%4)*13,left=burst?76:24,top=burst?25:34;sparks.push('<i class="firework-particle" style="left:'+left+'%;top:'+top+'%;--dx:'+Math.cos(angle)*distance+'px;--dy:'+Math.sin(angle)*distance+'px;--spark:'+CHORD_COLORS[(i+burst*4)%CHORD_COLORS.length]+';--delay:'+(burst*.14)+'s"></i>')}
  modal('<div class="fireworks" aria-hidden="true">'+sparks.join('')+'</div><div class="win-mark" aria-hidden="true">✦</div><h2>Поздравляем!</h2><p class="win-copy">Ты прошёл эту партию. Отличная работа!</p><div class="result-grid"><span>Сложность судоку</span><b>'+sudokuName(game.sudokuLevel)+'</b><span>Сложность аккордов</span><b>'+sudokuName(game.chordLevel)+'</b><span>Результат</span><b>'+score.toLocaleString('ru-RU')+' очков</b><span>Время</span><b>'+fmt(game.elapsed)+'</b><span>Ошибки · подсказки</span><b>'+game.errors+' · '+game.hints+'</b><span>Отмены · повторы</span><b>'+game.undos+' · '+game.redos+'</b><span>Лучший результат</span><b>'+best.toLocaleString('ru-RU')+'</b></div><div class="dialog-actions"><button class="btn" id="modalReview">Посмотреть поле</button><button class="btn primary" id="modalContinue">Продолжить</button></div>','win-dialog');
  $('#modalReview').onclick=()=>{winModalDismissed=true;renderModal()};$('#modalContinue').onclick=()=>openNewGameSettings({fromWin:true});return
 }
 if(!overlaySaved)return;
 modal('<h2>Продолжить партию?</h2><p>Найдена сохранённая незавершённая партия. Можно вернуться к ней или начать заново.</p><div class="dialog-actions"><button class="btn primary" id="continue">Продолжить</button><button class="btn" id="restart">Начать заново</button></div>');
 $('#continue').onclick=()=>{overlaySaved=false;render()};$('#restart').onclick=()=>openNewGameSettings({fromSaved:true})
}
function confirmNew(){openNewGameSettings({})}
function settings(){
 modal('<h2>Управление MIDI</h2><p>Сейчас: судоку — '+sudokuName(game.sudokuLevel)+'; аккорды — '+sudokuName(game.chordLevel)+'.</p><p>Без педали ноты До–Соль♯ выбирают блоки 1–9. При удержании педали они выбирают клетки 1–9 внутри выбранного блока. Три быстрых До — Undo, Ре — Redo, Соль — очистить выбранную клетку.</p><p>Перед распознаванием одиночной ноты приложение ждёт остальные ноты аккорда. MIDI работает на защищённой HTTPS-странице в браузерах с Web MIDI.</p><div class="setting-row"><span>Подсветка ошибок при вводе</span><button class="toggle '+(game.strict?'on':'')+'" id="instantToggle" aria-label="Подсветка ошибок при вводе"></button></div><div class="setting-row"><span>Не выключать экран</span><button class="toggle '+(wakeEnabled?'on':'')+'" id="wakeToggle" aria-label="Не выключать экран"'+(!navigator.wakeLock?' disabled':'')+'></button></div><p id="wakeStatus" class="wake-status"></p><div class="dialog-actions"><button class="btn primary" id="settingsDone">Готово</button></div>');
 $('#instantToggle').onclick=()=>{game.strict=!game.strict;$('#instantToggle').classList.toggle('on',game.strict);save()};$('#wakeToggle').onclick=()=>setWakeLockEnabled(!wakeEnabled);$('#settingsDone').onclick=()=>render();refreshWakeLockUI()
}
function selectPitch(pc){
 const index=NAV.findIndex(x=>x[1]===pc);if(index<0)return;
 if(pedal){const block=game.block??((game.selected/27|0)*3+(game.selected%9/3|0)),local=index;game.selected=((block/3|0)*3+(local/3|0))*9+(block%3)*3+local%3}
 else{const block=index,br=block/3|0,bc=block%3,sr=game.selected/9|0,sc=game.selected%9;game.block=block;game.selected=(br*3+sr%3)*9+bc*3+sc%3}
 game.wrong=[];save();render()
}
function executeTap(pc){pendingTap=null;tapTimer=null;selectPitch(pc)}
function handleSingleNote(note){
 const pc=note%12,now=Date.now();if(pc!==0&&pc!==2&&pc!==7){executeTap(pc);return}
 if(pendingTap&&pendingTap.pc===pc&&now-pendingTap.last<=TAP_WINDOW_MS){pendingTap.count++;pendingTap.last=now;if(pendingTap.count>=3){clearTimeout(tapTimer);pendingTap=null;tapTimer=null;if(pc===0)undo();else if(pc===2)redo();else clearCell();return}}
 else{if(pendingTap)executeTap(pendingTap.pc);pendingTap={pc,count:1,last:now}}
 clearTimeout(tapTimer);tapTimer=setTimeout(()=>{if(pendingTap)executeTap(pendingTap.pc)},TAP_WINDOW_MS)
}
function flushNotes(){const events=noteBatch;noteBatch=[];if(!events.length)return;const chord=recognized(events);if(chord){commit(chord);render();return}const unique=[...new Set(events.map(n=>n%12))];if(unique.length===1){events.forEach(n=>handleSingleNote(n));render()}}
function onMidi(e){const [status,n,v]=e.data,type=status&240;if(type===176&&n===64){pedal=v>=64;render();return}if(type===144&&v>0){held.add(n);noteBatch.push(n);clearTimeout(noteTimer);noteTimer=setTimeout(flushNotes,CHORD_WINDOW_MS);render()}else if(type===128||(type===144&&v===0)){held.delete(n);render()}}
function midiErrorText(error){if(!window.isSecureContext)return 'Для MIDI нужна защищённая HTTPS-страница.';if(!navigator.requestMIDIAccess)return midiBrowserMessage();if(error?.name==='NotAllowedError')return 'Браузер запретил MIDI. Разреши MIDI для beslanchick.github.io в настройках сайта и нажми «Подключить MIDI» ещё раз.';if(error?.name==='SecurityError')return 'Браузер заблокировал Web MIDI для этой страницы. Проверь разрешения сайта и открой его напрямую по HTTPS.';if(error?.name==='NotSupportedError')return midiBrowserMessage();return 'Не удалось открыть MIDI'+(error?.name?' ('+error.name+')':'')+'. Проверь разрешение MIDI для сайта и подключение клавиатуры.'}
function attachMidiAccess(access){if(midi&&midi!==access)midi.onstatechange=null;midi=access;midiError='';midi.onstatechange=updateInputs;updateInputs()}
async function requestMidiAccess(){if(!window.isSecureContext)throw Object.assign(new Error('Secure context required'),{name:'SecurityError'});if(!navigator.requestMIDIAccess)throw Object.assign(new Error('Web MIDI unavailable'),{name:'NotSupportedError'});if(!midiRequest)midiRequest=navigator.requestMIDIAccess({sysex:false}).then(access=>{attachMidiAccess(access);return access}).finally(()=>{midiRequest=null});return midiRequest}
async function connect(){
 midiError='';if(!window.isSecureContext||!navigator.requestMIDIAccess){midiError=midiErrorText();const status=$('#midiStatus');if(status)status.textContent=midiError;toast(midiError);return}
 const status=$('#midiStatus');if(status)status.textContent='Подключаем MIDI…';
 try{const access=await requestMidiAccess();const text=midiStatusText();toast(access.inputs.size?text:'Доступ разрешён. Подключи клавиатуру, если она ещё не подключена.');render()}
 catch(error){midiError=midiErrorText(error);const el=$('#midiStatus');if(el)el.textContent=midiError;toast(midiError)}
}
function updateInputs(){if(!midi)return;const next=new Map();for(const input of midi.inputs.values()){input.onmidimessage=onMidi;next.set(input.id,input)}for(const [id,input] of midiInputs)if(!next.has(id))input.onmidimessage=null;midiInputs=next;const el=$('#midiStatus');if(el)el.textContent=midiStatusText();const button=$('#connect');if(button)button.textContent=midi?'Переподключить MIDI':'Подключить MIDI'}
async function restoreGrantedMidiAccess(){if(!window.isSecureContext||!navigator.requestMIDIAccess||!navigator.permissions?.query)return;try{const permission=await navigator.permissions.query({name:'midi',sysex:false});if(permission.state==='granted'&&!midi){try{await requestMidiAccess()}catch{}}}catch{}}
function refreshWakeLockUI(){const toggle=$('#wakeToggle'),status=$('#wakeStatus');if(toggle){toggle.classList.toggle('on',wakeEnabled);toggle.disabled=!navigator.wakeLock}if(status){status.textContent=!navigator.wakeLock?'Этот браузер не поддерживает удержание экрана.':!wakeEnabled?'Выключено.':wakeLock&&!wakeLock.released?'Экран будет оставаться включённым, пока эта вкладка активна.':wakeError||'Экран включится, когда вкладка будет активна.'}}
function releaseWakeLock(){const current=wakeLock;wakeLock=null;if(current&&!current.released)current.release().catch(()=>{});refreshWakeLockUI()}
async function requestScreenWakeLock(){if(!wakeEnabled||document.visibilityState!=='visible')return null;if(!navigator.wakeLock){refreshWakeLockUI();return null}if(wakeLock&&!wakeLock.released)return wakeLock;if(wakeRequest)return wakeRequest;wakeError='';wakeRequest=navigator.wakeLock.request('screen').then(lock=>{if(!wakeEnabled){lock.release().catch(()=>{});return null}wakeLock=lock;lock.addEventListener('release',()=>{if(wakeLock===lock)wakeLock=null;refreshWakeLockUI()},{once:true});refreshWakeLockUI();return lock}).catch(error=>{wakeError=error?.name==='NotAllowedError'?'Браузер или система отказали. Проверь режим энергосбережения.':'Не удалось удержать экран ('+(error?.name||'ошибка')+').';return null}).finally(()=>{wakeRequest=null;refreshWakeLockUI()});return wakeRequest}
function setWakeLockEnabled(enabled){wakeEnabled=!!enabled;wakeError='';try{localStorage.setItem(WAKE_PREF,String(wakeEnabled))}catch{}if(wakeEnabled)requestScreenWakeLock();else releaseWakeLock();refreshWakeLockUI()}
function toggleTimer(){if(game.won)return;if(!game.timerPaused){game.elapsed=duration();game.timerPaused=true}else{game.started=Date.now();game.timerPaused=false}save();render()}
function tickTimer(){if(!game)return;if(timerNode)timerNode.textContent=fmt(duration());const button=$('#timerToggle');if(button){button.textContent=game.timerPaused?'▶':'Ⅱ';button.title=game.timerPaused?'Возобновить таймер':'Пауза таймера'}}
function keyHandler(e){
 if(e.target.matches('button,input,select'))return;
 if(e.key==='Escape'){if($('#hintPopover')&&!$('#hintPopover').classList.contains('hidden'))closeHintPopover();else if(!$('#modal').querySelector('.overlay'))toggleTimer()}
 if(['ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(e.key)){e.preventDefault();let i=game.selected,r=i/9|0,c=i%9;r=(r+(e.key==='ArrowDown'?1:e.key==='ArrowUp'?8:0))%9;c=(c+(e.key==='ArrowRight'?1:e.key==='ArrowLeft'?8:0))%9;game.selected=r*9+c;render()}
 if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='z')undo()
}
function toast(msg){const old=$('.notice');if(old)old.remove();const n=document.createElement('div');n.className='notice';n.textContent=msg;document.body.append(n);clearTimeout(notification);notification=setTimeout(()=>n.remove(),3000)}
function init(){
 try{wakeEnabled=localStorage.getItem(WAKE_PREF)!=='false'}catch{wakeEnabled=true}
 const saved=load();
 if(saved){game=saved;game.elapsed=Number(game.elapsed)||0;game.started=Date.now();game.timerPaused=false;overlaySaved=true;save()}
 else{game=fresh('easy','easy');game.timerPaused=true;overlaySaved=false}
 render();restoreGrantedMidiAccess();requestScreenWakeLock();if(!saved)openNewGameSettings({initial:true});tickTimer();setInterval(tickTimer,1000);document.addEventListener('visibilitychange',()=>{tickTimer();if(document.visibilityState==='visible'&&wakeEnabled)requestScreenWakeLock()});window.addEventListener('pagehide',()=>{save();releaseWakeLock()})
}
init();
})();
