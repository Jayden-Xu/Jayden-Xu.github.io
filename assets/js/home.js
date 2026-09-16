(function(){
'use strict';
const $=s=>document.querySelector(s);
const sections=[...document.querySelectorAll('.section')], buttons=[...document.querySelectorAll('.sectionLabels button')];
const content=$('#pageContent'), bg=$('#netBg');
const bgc=bg.getContext('2d');
const nav=$('.sectionLabels'),navCanvas=$('#navMatrix'),navCtx=navCanvas.getContext('2d');
const navStates=buttons.map(()=>({heat:0,kick:-Infinity}));
let navFields=[],navWidth=0,navHeight=0,navTime=0,navActive=-1,navHover=-1,navFocus=-1;
const motion=matchMedia('(prefers-reduced-motion: reduce)');
const clamp=(x,a=0,b=1)=>Math.max(a,Math.min(b,x));
const mix=(a,b,t)=>a+(b-a)*t;
const smooth=t=>t*t*t*(t*(t*6-15)+10); // C2 continuous: no velocity/acceleration jumps at camera boundaries.
const vMix=(a,b,t)=>a.map((v,i)=>mix(v,b[i],t));
let current=Math.max(0,sections.findIndex(s=>s.id===location.hash.slice(1)));
let transition=null, raf=0, lastBg=0, W=innerWidth,H=innerHeight,overlayDpr=1,resizeFrame=0;
let lastWheel=0,wheelSum=0, wheelTime=0, lastEnd=0, touch=null, pointer=null;
let renderer=null, renderFailed=false;
let pointerStamp=0, glowSprite=null, matrixBase=null, matrixCells=[];
let cellGlow=null, lastOverlay=0;
let touchHold=false, touchRelease=0;
const TOUCH_FADE=1500, POINTER_POWER=5;
// The fabric is lit only by the overlay: a warm pointer halo and the cool
// matrix cells that flicker on by themselves. Everything else stays dark.
// Ambient is near zero at rest, so unlit fabric stays invisible. A section
// change raises it for the length of the flight, then it fades back to dark.
const AMBIENT=.065, REVEAL=.30, REVEAL_IN=190, REVEAL_OUT=780;
// A dive opens the lens further still. Nothing is being read over the fabric
// at that point, so the exposure that keeps the wireframe quiet behind text is
// simply wasted — the close-up is the one moment the structure is the subject.
// It rides the flight's own progress, so brightness comes up with the move.
const DIVE_EXPOSURE=.34;
// Eight flow fields are solved per district kind. SLOTS is what the shader has
// room to evaluate per fragment and fixes the uniform sizes; LIVE is how many
// fronts actually fly, and may be fewer.
const SOURCES=8, SLOTS=3, LIVE=2;
const WARM=[1,.68,.36], COOL=[.60,.79,1], MAX_LIGHTS=6;
let activeCells=[], lights=[];
// Section anchors are neighboring districts in the same unbounded compute fabric.
const poses=[
 {target:[0,.55,0],dist:6.2,phi:.80,theta:.30},      // home       · radial package
 {target:[0,.80,-10],dist:5.7,phi:.70,theta:-.26},   // about      · tensor floorplan
 {target:[0,1.30,-20],dist:6.6,phi:.74,theta:.38},   // signals    · broadcast array
 {target:[0,1.60,-30],dist:6.8,phi:.86,theta:.46},   // experience · memory stacks
 {target:[0,.85,-40],dist:5.9,phi:.68,theta:-.38},   // projects   · switch fabric
 {target:[0,1.15,-50],dist:6.3,phi:.78,theta:.20},   // education  · substrate
 {target:[0,.75,-60],dist:5.5,phi:.92,theta:-.32}    // contact    · I/O portals
];
// Close-up poses. A section pose frames a whole district from outside; these
// park the camera inside one, on the single component an entry is filed under.
// An entry names one with data-focus; anything unnamed falls back to a dive
// straight down onto the middle of its own district.
const focusPoses={
 // Two things make these close-ups read as a focus rather than a step nearer:
 // the camera ends much closer than a section pose, and the lens goes long
 // (a narrow fov magnifies and flattens, the way racking in on a subject does).
 // broadcast array (z=-20): the mast and the dipoles on the outer wavefront
 'signal-mast':{target:[0,1.55,-20],dist:2.24,phi:.86,theta:.26,fov:.47},
 'signal-dipole':{target:[4.05,.62,-18.9],dist:1.98,phi:.94,theta:.78,fov:.47},
 // memory district (z=-30): the stacks
 'mem-stack-core':{target:[0,1.08,-30],dist:2.15,phi:.94,theta:.34,fov:.47},
 'mem-stack-west':{target:[-2.5,.70,-32.1],dist:2.06,phi:1.00,theta:-.52,fov:.47},
 'mem-stack-east':{target:[2.5,.86,-32.1],dist:2.06,phi:.98,theta:.62,fov:.47},
 // switch fabric (z=-40): the crossbar and its four port islands
 'switch-core':{target:[0,.82,-40],dist:1.98,phi:.82,theta:.16,fov:.47},
 'switch-arm-east':{target:[2.55,.58,-40],dist:2.06,phi:.86,theta:.72,fov:.47},
 'switch-arm-north':{target:[0,.58,-43.1],dist:2.06,phi:.86,theta:.08,fov:.47},
 // radial package (z=0) and tensor floorplan (z=-10), for entries filed there
 'package-die':{target:[0,.74,0],dist:2.06,phi:.80,theta:.30,fov:.47},
 'tensor-chiplet':{target:[2.18,.60,-12.18],dist:2.06,phi:.88,theta:.50,fov:.47}
};
const ZOOM_IN=1500, ZOOM_OUT=1150, DETAIL_DRIFT=.24;
// The flight and the panel are two states, never both: zoom holds the camera
// while it travels, detail holds it once it has arrived.
let zoom=null, detail=null;
// A trapezoid velocity profile: the rate climbs over the first RAMP of the
// move, holds flat through the middle, and falls over the last RAMP. Paired
// with the geometric distance blend this is an genuinely even zoom — the same
// magnification per unit time from start to finish — while still leaving and
// arriving at zero velocity, so there is no jolt in or out of the idle sway.
// An ease-in-out curve would instead be fastest at the midpoint and crawling
// at both ends, which is exactly what reads as the move changing its mind.
const RAMP=.22, RUSH_V=1/(1-RAMP);
const rush=t=>{
 t=clamp(t);
 if(t<RAMP)return RUSH_V*t*t/(2*RAMP);
 if(t>1-RAMP){const q=1-t;return 1-RUSH_V*q*q/(2*RAMP);}
 return RUSH_V*(RAMP/2+(t-RAMP));
};
// The same profile read as speed. Everything that should read as velocity —
// the streaks, the flare, the light band — is driven by this rather than by
// position, so they hold steady exactly while the camera is at full rate.
const surge=t=>{t=clamp(t);return t<RAMP?t/RAMP:t>1-RAMP?(1-t)/RAMP:1;};
// The one number the whole close-up runs on: 0 is the page, 1 is the close-up.
// The camera, the page copy, the panel and the streaks all read this same
// value, which is what keeps them from arriving in stages.
function zoomAmount(now){
 if(detail)return 1;
 if(!zoom)return 0;
 const u=rush(clamp((now-zoom.start)/zoom.span));
 return zoom.dir==='in'?u:1-u;
}
// Published to CSS so the 2D page is part of the same move as the 3D camera:
// the copy swells and dissolves as the lens closes on the component, and the
// panel resolves out of the same push rather than fading in afterwards.
let zoomPublished=-1;
function publishZoom(now){
 const k=zoomAmount(now);
 if(k===zoomPublished&&!zoom)return;
 zoomPublished=k;
 const style=document.documentElement.style;
 style.setProperty('--zoom',k.toFixed(4));
 // The copy clears early; the panel is held back to the last stretch of the
 // move, so most of the flight is spent looking at the fabric rather than at
 // a panel sliding over it. Both are ramps off the same clock, so neither
 // arrives as a separate stage.
 style.setProperty('--copy',smooth(clamp(k*1.55)).toFixed(4));
 style.setProperty('--panel',smooth(clamp((k-.52)/.48)).toFixed(4));
}

// Screen-space line segments: real 3D edges with a consistent, antialiased width.
// No solid faces, image textures, component labels, or component-specific colors.
function createPackage(canvas){
 const gl=canvas.getContext('webgl',{alpha:false,antialias:true,premultipliedAlpha:false,powerPreference:'low-power'});
 if(!gl)return null;
 const vs=`attribute vec3 aStart,aEnd;attribute vec2 aCorner;attribute vec4 aFlowA,aFlowB;attribute float aStrength;
 uniform mat4 uView,uProjection;uniform vec3 uOrigin;uniform vec2 uResolution;uniform float uPixelRatio;
 uniform vec4 uSelA[3],uSelB[3];
 varying vec3 vWorld,vPulse;varying float vEdge,vStrength;
 void main(){vec3 start=aStart+uOrigin,end=aEnd+uOrigin;vec4 ca=uProjection*uView*vec4(start,1.0),cb=uProjection*uView*vec4(end,1.0);
 vEdge=aCorner.y;vStrength=aStrength; vWorld=mix(start,end,aCorner.x);
 // Each vertex sits at one end of its segment, so it already carries that
 // end's flow values; the rasteriser interpolates them along the segment.
 vPulse=vec3(dot(aFlowA,uSelA[0])+dot(aFlowB,uSelB[0]),
             dot(aFlowA,uSelA[1])+dot(aFlowB,uSelB[1]),
             dot(aFlowA,uSelA[2])+dot(aFlowB,uSelB[2]));
 if(ca.w<.08||cb.w<.08){vStrength=0.0;gl_Position=vec4(2.0,2.0,2.0,1.0);return;}
 vec2 delta=(cb.xy/cb.w-ca.xy/ca.w)*uResolution;
 vec2 normal=vec2(-delta.y,delta.x)/max(length(delta),.001);
 vec4 position=mix(ca,cb,aCorner.x);position.xy+=normal*aCorner.y*(mix(1.2,3.4,clamp(aStrength,0.0,1.0))*uPixelRatio)/uResolution*position.w;gl_Position=position;}`;
 // Lights are supplied in screen space (top-left origin, device pixels) so the
 // 2D overlay and the 3D fabric are lit by exactly the same sources.
 const fs=`precision mediump float;varying vec3 vWorld,vPulse;varying float vEdge,vStrength;
 uniform vec3 uEye;uniform vec2 uViewport;
 uniform float uTime,uAmbient,uSweepHead,uSweepWidth,uSweepGain;
 uniform vec3 uSweepTint;
 uniform vec3 uPulseRadius,uPulseGain,uPulseTint;uniform float uPulseWidth,uPulseTail;
 // A front travelling out from its source, with a decaying wake behind it so
 // the structure it has already passed stays lit for a moment.
 float pulseAt(float flow,float radius,float gain){
  if(gain<=0.0)return 0.0;
  float d=radius-flow;
  float crest=1.0-smoothstep(0.0,uPulseWidth,abs(d));
  float wake=d>0.0?exp(-d/uPulseTail):0.0;
  return (crest*crest+wake*.34)*gain;
 }
 uniform vec4 uLights[6];uniform vec3 uLightColor[6];
 void main(){float aa=1.0-smoothstep(.38,1.0,abs(vEdge));
 float fog=1.0-smoothstep(11.0,27.0,length(vWorld.xz-uEye.xz));
 float activity=.94+.06*pow(max(0.0,sin(vWorld.z*1.4-uTime*2.0)),8.0);
 vec2 frag=vec2(gl_FragCoord.x,uViewport.y-gl_FragCoord.y);
 float total=0.0;vec3 tint=vec3(0.0);
 for(int i=0;i<6;i++){
  vec4 L=uLights[i];
  float f=1.0-smoothstep(0.0,L.z,distance(frag,L.xy));
  f=f*f*L.w;total+=f;tint+=uLightColor[i]*f;
 }
 if(uSweepGain>0.0){
  // Navigation front: screen space, because it belongs to the page, not the fabric.
  float f=1.0-smoothstep(0.0,1.0,abs(frag.x+frag.y-uSweepHead)/uSweepWidth);
  f=f*f*uSweepGain;total+=f;tint+=uSweepTint*f;
 }
 // Three signals fanning out from three of the eight sources at once, each on
 // its own clock. vPulse holds this point's distance from each of them.
 float pa=pulseAt(vPulse.x,uPulseRadius.x,uPulseGain.x);
 float pb=pulseAt(vPulse.y,uPulseRadius.y,uPulseGain.y);
 float pc=pulseAt(vPulse.z,uPulseRadius.z,uPulseGain.z);
 total+=pa+pb+pc;tint+=uPulseTint*(pa+pb+pc);
 vec3 tone=total>.0001?tint/total:vec3(.70,.78,.90);
 float alpha=aa*fog*vStrength*activity*(uAmbient+min(total,2.8));
 gl_FragColor=vec4(tone,alpha);}`;
 function shader(type,source){const s=gl.createShader(type);gl.shaderSource(s,source);gl.compileShader(s);if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw Error(gl.getShaderInfoLog(s));return s;}
 const program=gl.createProgram();gl.attachShader(program,shader(gl.VERTEX_SHADER,vs));gl.attachShader(program,shader(gl.FRAGMENT_SHADER,fs));gl.linkProgram(program);
 if(!gl.getProgramParameter(program,gl.LINK_STATUS))throw Error(gl.getProgramInfoLog(program));gl.useProgram(program);
 // Geometry is collected first so a flow field can be solved over it before
 // any vertices are emitted. Each segment remembers which district it belongs
 // to, since the field is solved in a district's local coordinates.
 const segs=[];let tagKind=0,tagOx=0,tagOz=0,tagDetail=false;
 function line(a,b,strength=.42){segs.push({a,b,s:strength,k:tagKind,ox:tagOx,oz:tagOz,d:tagDetail});}
 function ring(x,y,z,w,d,strength=.42){const a=[x-w/2,y,z-d/2],b=[x+w/2,y,z-d/2],c=[x+w/2,y,z+d/2],e=[x-w/2,y,z+d/2];line(a,b,strength);line(b,c,strength);line(c,e,strength);line(e,a,strength);}
 function cage(x,y,z,w,h,d,strength=.42){ring(x,y,z,w,d,strength);ring(x,y+h,z,w,d,strength);for(const dx of [-w/2,w/2])for(const dz of [-d/2,d/2])line([x+dx,y,z+dz],[x+dx,y+h,z+dz],strength);}
 // Feature hierarchy: broad package ribs, medium component edges, fine internal routing.
 function polygon(x,y,z,r,sides=8,strength=.72,angle=0){
  const points=[];for(let k=0;k<sides;k++){const a=angle+k*Math.PI*2/sides;points.push([x+Math.cos(a)*r,y,z+Math.sin(a)*r]);}
  for(let k=0;k<sides;k++)line(points[k],points[(k+1)%sides],strength);return points;
 }
 function grid(x,y,z,w,d,n,strength=.34){ring(x,y,z,w,d,.64);for(let k=1;k<n;k++){line([x-w/2+w*k/n,y,z-d/2],[x-w/2+w*k/n,y,z+d/2],strength);line([x-w/2,y,z-d/2+d*k/n],[x+w/2,y,z-d/2+d*k/n],strength);}}
 function ports(x,y,z,w,d,n){for(let k=0;k<n;k++){const q=(k+.5)/n;for(const side of [-1,1]){line([x-w/2+w*q,y,z+side*d/2],[x-w/2+w*q,y-.27,z+side*(d/2+.30)],.47);line([x+side*w/2,y,z-d/2+d*q],[x+side*(w/2+.30),y-.27,z-d/2+d*q],.47);}}}
 function district(kind,x,z,detailed){
  cage(x,-.48,z,8.75,.24,8.75,.48);ring(x,-.14,z,8.35,8.35,.63);
  if(detailed){
   ports(x,-.15,z,8.35,8.35,18);for(let k=1;k<5;k++)ring(x,-.44+k*.055,z,8.65,8.65,.22);
   for(const side of [-1,1])for(let k=0;k<14;k++){
    const q=-3.4+k*.52;ring(x+side*3.85,-.10,z+q,.24,.32,.34);
    line([x+q,-.11,z+side*4.08],[x+q+.22,-.11,z+side*3.72],.25);
   }
  }
  if(kind===0){ // Radial package: concentric octagonal decks, spokes and satellite tiles.
   const levels=detailed?5:2;
   for(let j=0;j<levels;j++)polygon(x,j*.15,z,3.60-j*.24,8,.72,Math.PI/8);
   const top=polygon(x,.75,z,2.12,8,.84,Math.PI/8),bottom=polygon(x,-.05,z,2.65,8,.56,Math.PI/8);
   for(let k=0;k<8;k++){line(top[k],bottom[k],.7);const a=Math.PI/8+k*Math.PI/4;line([x+Math.cos(a)*.68,.76,z+Math.sin(a)*.68],top[k],.57);}
   polygon(x,.76,z,.68,8,.87,Math.PI/8);grid(x,.30,z,1.05,1.05,detailed?7:2,.35);
   if(detailed){
    for(let j=1;j<6;j++)polygon(x,.755-j*.035,z,.68+j*.28,8,.38,Math.PI/8);
    for(let k=0;k<32;k++){const a=Math.PI/8+k*Math.PI/16;line([x+Math.cos(a)*.73,.76,z+Math.sin(a)*.73],[x+Math.cos(a)*2.06,.60,z+Math.sin(a)*2.06],k%4?.28:.56);}
   }
   if(detailed)for(let k=0;k<8;k++){const a=k*Math.PI/4;const px=x+Math.cos(a)*3.45,pz=z+Math.sin(a)*3.45;cage(px,0,pz,.72,.4,.72,.54);grid(px,.4,pz,.56,.56,4,.28);}
  }else if(kind===1){ // Tensor floorplan: nine chiplets, hierarchical meshes, crossbar channels.
   for(let row=-1;row<=1;row++)for(let col=-1;col<=1;col++){
    const px=x+col*2.18,pz=z+row*2.18,h=col===0&&row===0?.82:.43;
    cage(px,-.05,pz,1.91,h,1.91,.75);ring(px,h-.05,pz,1.65,1.65,.53);grid(px,h-.04,pz,1.38,1.38,detailed?8:2,.34);
    if(detailed)for(let r=-1;r<=1;r++)for(let c=-1;c<=1;c++)ring(px+c*.43,h-.03,pz+r*.43,.30,.30,.38);
   }
   for(const side of [-1,1])for(let k=0;k<(detailed?8:2);k++){const q=side*(1.01+k*.025);line([x+q,.03,z-3.7],[x+q,.03,z+3.7],.45);line([x-3.7,.03,z+q],[x+3.7,.03,z+q],.45);}
  }else if(kind===2){ // Broadcast array: a mast over concentric wavefronts, dipoles standing on the rim.
   const levels=detailed?5:3,SIDES=12,rings=[];
   for(let j=0;j<levels;j++)rings.push(polygon(x,.02+j*.05,z,1.35+j*(detailed?.72:1.2),SIDES,j?.42:.62,Math.PI/SIDES));
   // Radial ribs tie the wavefronts together — visually, and for the flow field,
   // which can only travel along geometry that actually meets.
   for(let j=1;j<rings.length;j++)for(let k=0;k<SIDES;k++)line(rings[j-1][k],rings[j][k],k%3?.26:.50);
   for(let k=0;k<SIDES;k+=2)line([x,.05,z],rings[0][k],.38);
   cage(x,0,z,.62,2.15,.62,.80);
   const bands=detailed?9:3;for(let j=1;j<bands;j++)ring(x,j*2.15/bands,z,.62,.62,.34);
   const crown=polygon(x,2.18,z,.95,8,.85,Math.PI/8),collar=polygon(x,1.55,z,.44,8,.58,Math.PI/8);
   for(let k=0;k<8;k++)line(crown[k],collar[k],.50);
   const outer=rings[rings.length-1];
   for(let k=0;k<SIDES;k+=detailed?2:4){
    const q=outer[k];
    line(q,[q[0],q[1]+.85,q[2]],.62);ring(q[0],q[1]+.85,q[2],.34,.34,.45);
    if(detailed)line([q[0],q[1]+.85,q[2]],[q[0],q[1]+1.25,q[2]],.40);
   }
  }else if(kind===3){ // Memory: tall stacks, staggered terraces and vertical vias.
   const sites=[[0,0,2.10],[-2.50,-2.1,1.35],[2.5,-2.1,1.68],[-2.5,2.1,.95],[2.5,2.1,1.32]];
   for(const [dx,dz,h]of sites){const px=x+dx,pz=z+dz;cage(px,-.02,pz,1.85,h,2.25,.82);
    const count=detailed?10:3;for(let j=1;j<count;j++)ring(px,h*j/count-.02,pz,1.85,2.25,.45);
    grid(px,h-.02,pz,1.58,1.94,detailed?6:2,.40);
    if(detailed)for(let k=1;k<7;k++){const q=-.87+k*.25;line([px+q,0,pz-1.125],[px+q,h,pz-1.125],.35);}
   }
   if(detailed)for(let k=0;k<12;k++){const q=(k-5.5)*.12;line([x+q,-.08,z-4],[x+q,-.08,z+4],.35);}
  }else if(kind===4){ // Switch fabric: crossing bridges, diagonal routes and port islands.
   cage(x,.22,z,2.50,.55,2.5,.85);polygon(x,.79,z,1.06,8,.76);grid(x,.8,z,1.20,1.20,detailed?8:3,.36);
   for(let arm=0;arm<4;arm++){
    const a=arm*Math.PI/2,dx=Math.cos(a),dz=Math.sin(a),nx=-dz,nz=dx;
    cage(x+dx*3.1,-.02,z+dz*3.1,1.40,.50,1.40,.68);
    for(let k=0;k<(detailed?16:4);k++){
     const q=(k/((detailed?16:4)-1)-.5)*.86;
     const points=[[x+dx*1.20+nx*q,.57,z+dz*1.20+nz*q],[x+dx*1.8+nx*q,1.12,z+dz*1.8+nz*q],[x+dx*2.6+nx*q,1.12,z+dz*2.6+nz*q],[x+dx*3.1+nx*q,.50,z+dz*3.1+nz*q]];
     for(let j=0;j<3;j++)line(points[j],points[j+1],k%4?.39:.67);
    }
    if(detailed)grid(x+dx*3.1,.49,z+dz*3.1,1.16,1.16,5,.34);
   }
  }else if(kind===5){ // Substrate: terraced routing layers, ribs and through-layer channels.
   const n=detailed?8:4;
   for(let j=0;j<n;j++){const h=j*.15,w=7-j*.48;ring(x,h,z,w,w,.66);if(detailed)for(let k=1;k<10;k++){const q=-w/2+k*w/10;line([x+q,h,z-w/2],[x+q,h,z+w/2],.25);}}
   for(const dx of [-1.32,1.32])for(const dz of [-1.32,1.32]){cage(x+dx,0,z+dz,.46,1.5,.46,.76);if(detailed)for(let j=1;j<8;j++)ring(x+dx,j*.18,z+dz,.46,.46,.4);}
   grid(x,1.18,z,2.0,2.0,detailed?10:3,.45);
  }else{ // I/O: nested vertical portals, long connector combs and twin cable banks.
   for(let j=0;j<(detailed?8:3);j++){
    const depth=z-j*.28,w=2.4+j*.18,h=1.20+j*.10;
    const pts=[[x-w/2,.10,depth],[x-w/2,h,depth],[x+w/2,h,depth],[x+w/2,.10,depth]];
    for(let k=0;k<4;k++)line(pts[k],pts[(k+1)%4],j===0?.86:.46);
   }
   for(const side of [-1,1]){
    cage(x+side*2.7,0,z,1.14,.9,5.8,.76);
    const n=detailed?20:5;for(let j=0;j<n;j++){const q=-2.6+j*5.2/(n-1);ring(x+side*2.7,.9,z+q,1.05,.12,.50);line([x+side*2.7,.88,z+q],[x+side*1.8,.15,z+q],.43);}
   }
   if(detailed)for(let k=0;k<16;k++){const q=(k-7.5)*.12;line([x+q,.08,z+3.5],[x+q,.08,z-3.5],.42);}
  }
 }
 // Seven distinct detailed landmarks, one per section; surrounding low-detail
 // districts continue the landscape past the view frustum without repeating
 // one identical tile.
 for(let row=-9;row<=4;row++)for(let col=-4;col<=4;col++){
  const kind=((-row+col*2)%7+7)%7;
  tagKind=kind;tagOx=col*10;tagOz=row*10;tagDetail=col===0&&row<=0&&row>=-6;
  district(kind,col*10,row*10,tagDetail);
  for(const side of [-1,1]){
   line([col*10-5,-.2,row*10+side*4.8],[col*10+5,-.2,row*10+side*4.8],.30);
   line([col*10+side*4.8,-.2,row*10-5],[col*10+side*4.8,-.2,row*10+5],.30);
  }
 }

 // ---- flow field ----------------------------------------------------------
 // How far the signal has to travel *through the structure* to reach a point,
 // measured from the die at the district's centre. Districts of one kind are
 // identical up to translation, so each field is solved once and reused.
 //
 // Nodes are the segment endpoints. Edges are the segments themselves plus
 // short hops between endpoints that sit close together, which is what stitches
 // a grid's interior lines to the ring they end on — those meet the ring part
 // way along an edge, so they share no endpoint with it. HOP bounds how far the
 // signal will jump, and because nodes only exist where geometry does, a path
 // still has to follow the structure rather than cut across open space.
 // HOP is tuned to the widest gap the structure actually leaves between two
 // pieces that belong together — the memory district parks its stacks .65
 // apart, so anything under that strands them on an island of their own.
 const HOP=1.0,CELL=1.2,REACH=1.0;
 const d3=(a,b)=>Math.hypot(a[0]-b[0],a[1]-b[1],a[2]-b[2]);
 const cellKey=p=>Math.floor(p[0]/CELL)+':'+Math.floor(p[1]/CELL)+':'+Math.floor(p[2]/CELL);
 function neighbours(hash,p,out){
  out.length=0;
  const cx=Math.floor(p[0]/CELL),cy=Math.floor(p[1]/CELL),cz=Math.floor(p[2]/CELL);
  for(let i=-1;i<=1;i++)for(let j=-1;j<=1;j++)for(let k=-1;k<=1;k++){
   const b=hash.get((cx+i)+':'+(cy+j)+':'+(cz+k));if(b)for(const n of b)out.push(n);
  }
  return out;
 }
 function buildField(kind){
  const index=new Map(),pts=[],adj=[];
  const id=p=>{
   const key=Math.round(p[0]*500)+':'+Math.round(p[1]*500)+':'+Math.round(p[2]*500);
   let i=index.get(key);
   if(i===undefined){i=pts.length;index.set(key,i);pts.push(p);adj.push([]);}
   return i;
  };
  const link=(i,j,w)=>{adj[i].push(j,w);adj[j].push(i,w);};
  for(const seg of segs){
   if(seg.k!==kind||!seg.d)continue;
   const a=[seg.a[0]-seg.ox,seg.a[1],seg.a[2]-seg.oz],b=[seg.b[0]-seg.ox,seg.b[1],seg.b[2]-seg.oz];
   const i=id(a),j=id(b);if(i!==j)link(i,j,d3(pts[i],pts[j]));
  }
  const hash=new Map();
  pts.forEach((p,i)=>{const k=cellKey(p);let b=hash.get(k);if(!b)hash.set(k,b=[]);b.push(i);});
  const near=[];
  for(let i=0;i<pts.length;i++)for(const j of neighbours(hash,pts[i],near)){
   if(j<=i)continue;const w=d3(pts[i],pts[j]);if(w<=HOP)link(i,j,w);
  }
  // Dijkstra out from the die: everything standing over the district's centre.
  const D=new Float64Array(pts.length).fill(Infinity),heap=[];
  const push=(d,i)=>{heap.push(d,i);let c=heap.length/2-1;
   while(c>0){const par=(c-1)>>1;if(heap[par*2]<=heap[c*2])break;
    for(let o=0;o<2;o++){const t=heap[par*2+o];heap[par*2+o]=heap[c*2+o];heap[c*2+o]=t;}c=par;}};
  const pop=()=>{const d=heap[0],i=heap[1],n=heap.length/2-1;
   heap[0]=heap[n*2];heap[1]=heap[n*2+1];heap.length=n*2;
   let c=0;for(;;){const l=c*2+1,r=l+1;let m=c;
    if(l<n&&heap[l*2]<heap[m*2])m=l;if(r<n&&heap[r*2]<heap[m*2])m=r;if(m===c)break;
    for(let o=0;o<2;o++){const t=heap[m*2+o];heap[m*2+o]=heap[c*2+o];heap[c*2+o]=t;}c=m;}
   return [d,i];};
  // Source 0 is the die at the centre. The other seven are spread by farthest
  // point sampling, so signals also start out at the edges of the district
  // rather than always from the middle.
  const seeds=[];
  let closest=Infinity,closestI=0;
  pts.forEach((p,i)=>{const r=Math.hypot(p[0],p[2]);if(r<closest){closest=r;closestI=i;}});
  seeds.push(closestI);
  const spread=new Float64Array(pts.length).fill(Infinity);
  while(seeds.length<SOURCES){
   const s=pts[seeds[seeds.length-1]];
   let far=-1,farI=0;
   for(let i=0;i<pts.length;i++){
    const d=d3(pts[i],s);if(d<spread[i])spread[i]=d;
    if(spread[i]>far){far=spread[i];farI=i;}
   }
   seeds.push(farI);
  }
  const fields=seeds.map(seed=>{
   D.fill(Infinity);heap.length=0;
   D[seed]=0;push(0,seed);
   while(heap.length){
    const [d,i]=pop();if(d>D[i])continue;
    const a=adj[i];
    for(let n=0;n<a.length;n+=2){const j=a[n],nd=d+a[n+1];if(nd<D[j]){D[j]=nd;push(nd,j);}}
   }
   let maxD=0;for(const d of D)if(isFinite(d)&&d>maxD)maxD=d;
   if(!maxD)maxD=1;
   // Anything a signal never reaches lights last rather than never.
   const out=new Float32Array(D.length);
   for(let i=0;i<D.length;i++)out[i]=isFinite(D[i])?D[i]/maxD:1;
   return out;
  });
  return {pts,fields,hash,memo:new Map()};
 }
 const fields=[0,1,2,3,4,5,6].map(buildField);
 // Segments share endpoints heavily, so the same local point is asked for many
 // times over; memoising turns most of ~40k lookups into a map hit.
 const lookupBuf=[];
 function flowAt(field,p){
  const key=Math.round(p[0]*500)+':'+Math.round(p[1]*500)+':'+Math.round(p[2]*500);
  const hit=field.memo.get(key);if(hit)return hit;
  let best=Infinity,node=-1;
  for(const i of neighbours(field.hash,p,lookupBuf)){
   const d=d3(field.pts[i],p);if(d<best){best=d;node=i;}
  }
  const out=new Float32Array(SOURCES);
  if(best<=REACH&&node>=0)for(let k=0;k<SOURCES;k++)out[k]=field.fields[k][node];
  else out.fill(1);
  field.memo.set(key,out);return out;
 }

 const STRIDE=9+SOURCES,CORNERS=[[0,-1],[1,-1],[1,1],[0,-1],[1,1],[0,1]];
 const vertices=new Float32Array(segs.length*6*STRIDE);
 let o=0;
 for(const seg of segs){
  const f=fields[seg.k];
  const fa=flowAt(f,[seg.a[0]-seg.ox,seg.a[1],seg.a[2]-seg.oz]);
  const fb=flowAt(f,[seg.b[0]-seg.ox,seg.b[1],seg.b[2]-seg.oz]);
  for(const c of CORNERS){
   vertices[o++]=seg.a[0];vertices[o++]=seg.a[1];vertices[o++]=seg.a[2];
   vertices[o++]=seg.b[0];vertices[o++]=seg.b[1];vertices[o++]=seg.b[2];
   vertices[o++]=c[0];vertices[o++]=c[1];vertices[o++]=seg.s;
   const fl=c[0]?fb:fa;
   for(let k=0;k<SOURCES;k++)vertices[o++]=fl[k];
  }
 }
 const segCount=segs.length;segs.length=0;
 const buf=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,buf);gl.bufferData(gl.ARRAY_BUFFER,vertices,gl.STATIC_DRAW);
 [['aStart',3,0],['aEnd',3,12],['aCorner',2,24],['aStrength',1,32],['aFlowA',4,36],['aFlowB',4,52]].forEach(([name,size,offset])=>{const a=gl.getAttribLocation(program,name);gl.enableVertexAttribArray(a);gl.vertexAttribPointer(a,size,gl.FLOAT,false,STRIDE*4,offset);});
 const u={};['uView','uProjection','uEye','uOrigin','uResolution','uViewport','uPixelRatio','uTime','uAmbient','uSweepHead','uSweepWidth','uSweepGain','uSweepTint','uSelA[0]','uSelB[0]','uPulseRadius','uPulseGain','uPulseTint','uPulseWidth','uPulseTail','uLights[0]','uLightColor[0]'].forEach(n=>u[n]=gl.getUniformLocation(program,n));
 const lightData=new Float32Array(MAX_LIGHTS*4),colorData=new Float32Array(MAX_LIGHTS*3);
 const selA=new Float32Array(SLOTS*4),selB=new Float32Array(SLOTS*4);
 const radii=new Float32Array(SLOTS),gains=new Float32Array(SLOTS);
 const norm=v=>{const l=Math.hypot(...v);return v.map(x=>x/l);};const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
 // `roll` banks the camera about its own view axis. Nothing on screen is
 // re-aimed by it, so it buys drama without ever breaking the line of a move.
 function view(eye,target,roll){const z=norm(eye.map((v,i)=>v-target[i]));let x=norm(cross([0,1,0],z)),y=cross(z,x);
 if(roll){const c=Math.cos(roll),sn=Math.sin(roll),rx=x.map((v,i)=>v*c+y[i]*sn);y=y.map((v,i)=>v*c-x[i]*sn);x=rx;}
 return new Float32Array([x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-dot(x,eye),-dot(y,eye),-dot(z,eye),1]);}
 let aspect=1,dpr=1;
 function resize(){dpr=Math.min(devicePixelRatio||1,1.6,Math.sqrt(2200000/(W*H)));canvas.width=Math.round(W*dpr);canvas.height=Math.round(H*dpr);aspect=W/H;gl.viewport(0,0,canvas.width,canvas.height);}
 function render(p,time,lights,sweep,ambient,pulses){
  const distance=p.distance*(aspect<.75?1.18:1),sp=Math.sin(p.phi),cp=Math.cos(p.phi);
  const eye=[p.target[0]+distance*sp*Math.sin(p.theta),p.target[1]+distance*cp,p.target[2]+distance*sp*Math.cos(p.theta)];
  const f=1/Math.tan((p.fov||.69)/2),near=.08,far=90;const proj=new Float32Array([f/aspect,0,0,0,0,f,0,0,0,0,(far+near)/(near-far),-1,0,0,2*far*near/(near-far),0]);
  gl.clearColor(0,0,0,1);gl.clear(gl.COLOR_BUFFER_BIT);gl.disable(gl.DEPTH_TEST);gl.enable(gl.BLEND);gl.blendFunc(gl.SRC_ALPHA,gl.ONE);
  for(let i=0;i<MAX_LIGHTS;i++){
   const L=lights&&lights[i];
   lightData[i*4]=L?L.x*dpr:0;lightData[i*4+1]=L?L.y*dpr:0;
   lightData[i*4+2]=L?Math.max(1,L.r*dpr):1;lightData[i*4+3]=L?L.i:0;
   colorData[i*3]=L?L.c[0]:0;colorData[i*3+1]=L?L.c[1]:0;colorData[i*3+2]=L?L.c[2]:0;
  }
  gl.uniform4fv(u['uLights[0]'],lightData);gl.uniform3fv(u['uLightColor[0]'],colorData);
  gl.uniform1f(u.uAmbient,ambient);
  gl.uniform1f(u.uSweepHead,sweep?sweep.head*dpr:0);
  gl.uniform1f(u.uSweepWidth,sweep?Math.max(1,sweep.width*dpr):1);
  gl.uniform1f(u.uSweepGain,sweep?sweep.gain:0);
  gl.uniform3fv(u.uSweepTint,sweep?sweep.tint:FRONT_TINT);
  selA.fill(0);selB.fill(0);
  for(let i=0;i<SLOTS;i++){
   const q=pulses&&pulses[i];
   radii[i]=q?q.radius:0;gains[i]=q?q.gain:0;
   if(q)(q.field<4?selA:selB)[i*4+(q.field&3)]=1;
  }
  gl.uniform4fv(u['uSelA[0]'],selA);gl.uniform4fv(u['uSelB[0]'],selB);
  gl.uniform3fv(u.uPulseRadius,radii);gl.uniform3fv(u.uPulseGain,gains);
  gl.uniform3fv(u.uPulseTint,PULSE_TINT);
  gl.uniform1f(u.uPulseWidth,PULSE_WIDTH);gl.uniform1f(u.uPulseTail,PULSE_TAIL);
  gl.uniformMatrix4fv(u.uView,false,view(eye,p.target,p.roll||0));gl.uniformMatrix4fv(u.uProjection,false,proj);gl.uniform3fv(u.uEye,eye);gl.uniform3fv(u.uOrigin,[0,0,0]);gl.uniform2f(u.uResolution,canvas.width,canvas.height);gl.uniform2f(u.uViewport,canvas.width,canvas.height);gl.uniform1f(u.uPixelRatio,dpr);gl.uniform1f(u.uTime,time/1000);gl.drawArrays(gl.TRIANGLES,0,segCount*6);
 }
 canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();renderFailed=true;if(transition)finish();});
 resize();return {resize,render};
}

// The fabric is always on screen, so navigation is one short camera flight
// across it while the text panels slide past — no full-screen takeover.
const DURATION=900, OUT_END=240, IN_START=330, IN_END=860;
// Distance is interpolated geometrically, not linearly: halving the distance
// looks like the same amount of zoom whether it happens at 6 units or at 2, so
// a constant ratio per unit time is what reads as one even, continuous move.
// Linear interpolation crawls at the far end and slams at the near end, which
// is most of why the old flight felt like it changed its mind halfway.
function blendPose(a,b,t,tFov){
 const da=Math.max(.05,a.dist),db=Math.max(.05,b.dist);
 return {target:vMix(a.target,b.target,t),distance:da*Math.pow(db/da,t),theta:mix(a.theta,b.theta,t),phi:mix(a.phi,b.phi,t),fov:mix(a.fov||.69,b.fov||.69,tFov===undefined?t:tFov),roll:0};
}
// Drift is added on top of whatever base pose is active, so resuming the idle
// sway at the end of a flight produces no jump.
// Up close the same sway would swing the camera through the structure, so the
// amplitude scales with how far in the flight has travelled.
function applyDrift(p,now,k=1){
 if(motion.matches)return p;
 const t=now/1000;
 p.target=[p.target[0]+Math.sin(t*.13)*.30*k,p.target[1]+Math.sin(t*.09)*.10*k,p.target[2]+Math.cos(t*.11)*.26*k];
 p.theta+=Math.sin(t*.062)*.09*k;p.phi+=Math.sin(t*.051)*.022*k;p.distance+=Math.sin(t*.073)*.12*k;
 return p;
}
function cameraPose(now){
 let p,drift=1;
 if(zoom){
  // One unbroken move. Every quantity below is monotonic in `k`, so there is
  // no point in the flight where the camera reverses, pauses, or re-aims: it
  // leaves the district pose and arrives at the component pose, and the only
  // thing that varies is how fast it is going.
  const k=zoomAmount(now);
  // The lens runs ahead of the dolly — it is already most of the way to its
  // long setting while the camera is still closing. Focal length and distance
  // pulling against each other is the Vertigo warp, and it is what makes the
  // structure swell through the middle of the move instead of merely growing.
  p=blendPose(poses[current],zoom.pose,k,clamp(k*1.32));
  // A bank into the move: rotation about the view axis only, so nothing on
  // screen is re-aimed — it reads as speed without costing continuity.
  p.roll=Math.sin(Math.PI*k)*.11*(zoom.dir==='in'?1:-1);
  drift=mix(1,DETAIL_DRIFT,k);
 }else if(detail){
  p=blendPose(detail.pose,detail.pose,0);drift=DETAIL_DRIFT;
 }else if(transition){
  const u=smooth(clamp((now-transition.start)/DURATION)),arc=Math.sin(Math.PI*u);
  p=blendPose(poses[transition.from],poses[transition.to],u);
  p.distance+=arc*2.9;p.phi+=arc*.10;
 }else p=blendPose(poses[current],poses[current],0);
 return applyDrift(p,now,drift);
}
// A finger is a light too, but it leaves the glass; after release the halo
// lingers and fades instead of snapping off.
function pointerPower(now){
 if(!pointer)return 0;
 if(!pointer.touch||touchHold)return POINTER_POWER;
 const q=(now-touchRelease)/TOUCH_FADE;
 return q>=1?0:POINTER_POWER*(1-smooth(q));
}
// Lights the fabric sees: the warm pointer halo always wins a slot, the rest
// go to whichever matrix cells happen to be lit right now.
function sceneLights(now){
 lights.length=0;
 const power=pointerPower(now);
 if(pointer&&power<=0&&pointer.touch)pointer=null;
 const cells=activeCells.slice().sort((a,b)=>b.e-a.e);
 for(const a of cells){
  if(lights.length>=MAX_LIGHTS-(power>0?1:0))break;
  lights.push({x:a.x+9,y:a.y+9,r:138,i:a.e*.95,c:COOL});
 }
 if(power>0)lights.unshift({x:pointer.x,y:pointer.y,r:330,i:power,c:WARM});
 return lights;
}
// One wave clock drives both the 2D matrix pulse and the light band that
// sweeps across the model, so they read as the same event.
// Exposure: full through the flight, then a slow decay measured from the
// moment the transition ended, so the fabric sinks back into the dark.
function revealAmount(now){
 // Nothing is reading over the fabric during a dive, so it stays fully lit.
 if(zoom||detail)return 1;
 if(transition)return smooth(clamp((now-transition.start)/REVEAL_IN));
 if(!lastEnd)return 0;
 const q=(now-lastEnd)/REVEAL_OUT;
 return q>=1?0:1-smooth(q);
}
// Two different waves, two different shapes. Navigating fires a directional
// front across the diagonal; at rest the fabric breathes — a ring collapses
// from the rim onto the landmark at the centre of frame, pauses, and expands
// back out. Cells the wave crosses ignite and fade in its wake.
const PULSE_TINT=[.80,.89,1], FRONT_TINT=[1,.69,.36];
// Flow runs 0 at a source to 1 at the furthest point it reaches, so a front
// overshoots slightly to clear the structure entirely before it is retired.
const PULSE_REACH=1.16, PULSE_WIDTH=.075, PULSE_TAIL=.26, PULSE_GAIN=1.2;
// Fronts run continuously and independently rather than on one shared clock:
// each retires at the far edge and comes back somewhere else, so the fabric is
// never idle and never repeats the same figure twice in a row.
const flights=[];
function seedFlights(now){
 flights.length=0;
 for(let i=0;i<LIVE;i++)flights.push({field:i*3%SOURCES,start:now+i*1900,span:5000});
}
function retireFlight(f,now,taken){
 let next;do{next=Math.floor(Math.random()*SOURCES);}while(SOURCES>LIVE&&taken.has(next));
 taken.add(next);
 f.field=next;f.start=now+Math.random()*1600;f.span=4400+Math.random()*2800;
}
// The navigation front stays in screen space: it belongs to the page turn.
function sceneSweep(now){
 if(zoom){
  // Same band of light, read as speed rather than as a page turn — but kept
  // low. It only grazes the wireframe as it passes; the move itself is what
  // is meant to be doing the work, so the light must not out-shout it.
  const t=clamp((now-zoom.start)/zoom.span),forward=zoom.dir==='in';
  const v=surge(t),reach=W+H,pad=520;
  return {kind:'warp',t,v,forward,tint:FRONT_TINT,
   head:(forward?t:1-t)*(reach+pad*2)-pad,width:420,
   gain:v*.85};
 }
 if(!transition)return null;
 const t=clamp((now-transition.start)/DURATION),forward=transition.forward;
 const span=W+H,pad=460;
 return {kind:'front',t,forward,amp:.30,tint:FRONT_TINT,
  head:(forward?t:1-t)*(span+pad*2)-pad,width:250,
  gain:Math.min(1,t*10,(1-t)*10)*1.7};
}
// Each flight is a front fanning out from one of the eight sources, riding the
// flow field: a band in "distance travelled through the wires", so it crawls
// the structure the way a signal would — out along the spokes, around a ring
// from wherever the spoke met it, up a memory column — instead of expanding as
// a circle. Every section is parked on a different district, so every section
// propagates differently.
function scenePulses(now){
 if(motion.matches)return null;
 if(!flights.length)seedFlights(now);
 const taken=new Set(flights.map(f=>f.field));
 for(const f of flights)if(now>=f.start+f.span){taken.delete(f.field);retireFlight(f,now,taken);}
 return flights.map(f=>{
  const t=(now-f.start)/f.span;
  if(t<0||t>1)return {field:f.field,radius:0,gain:0};
  return {field:f.field,radius:t*PULSE_REACH,gain:Math.min(1,t*9,(1-t)*3.2)*PULSE_GAIN};
 });
}
function labels(){
 if(navActive!==current){navStates[current].kick=performance.now();navActive=current;}
 buttons.forEach((b,i)=>{if(i===current)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current');});
 $('#progressFill').style.transform='scaleX('+(current/(sections.length-1))+')';
 sections.forEach((s,i)=>{s.inert=i!==current;s.setAttribute('aria-hidden',String(i!==current));s.classList.toggle('is-active',i===current);});
}
function bodyOf(el){return el&&(el.firstElementChild||el);}
function clearFeature(el){
 if(!el)return;
 el.style.transform='';el.style.willChange='';
 const body=bodyOf(el);body.style.opacity='';body.style.willChange='';
}
function slideFeature(el,px,opacity){
 el.style.transform='translate3d(0,'+px.toFixed(1)+'px,0)';
 bodyOf(el).style.opacity=String(opacity);
}
function snap(){window.scrollTo(0,sections[current].offsetTop);}
function finish(){
 if(!transition)return;
 const tr=transition;transition=null;
 clearFeature(tr.outEl);clearFeature(tr.inEl);
 content.inert=false;snap();labels();
 sections[current].focus({preventScroll:true});lastEnd=performance.now();lastBg=0;
 document.body.dataset.phase='content';document.body.dataset.heartbeat=motion.matches?'off':'waiting';
 ensureFrame();
}
function go(index,historyMode=true){
 index=clamp(index,0,sections.length-1);if(index===current||transition||zoom||detail)return;
 const from=current;current=index;
 if(historyMode)history.replaceState(null,'','#'+sections[current].id);
 labels();
 if(motion.matches||!renderer||renderFailed){snap();sections[current].focus({preventScroll:true});lastBg=0;ensureFrame();return;}
 const forward=index>from;
 const outEl=sections[from].querySelector('.section-inner'),inEl=sections[index].querySelector('.section-inner');
 transition={from,to:index,start:performance.now(),forward,outEl,inEl,snapped:false,shift:clamp(H*.073,28,86)};
 outEl.style.willChange='transform';inEl.style.willChange='transform';
 bodyOf(outEl).style.willChange='opacity';bodyOf(inEl).style.willChange='opacity';
 slideFeature(inEl,forward?transition.shift:-transition.shift,0);
 content.inert=true;document.body.dataset.heartbeat='off';
 ensureFrame();
}
// Straight vertical hand-off: the old panel travels out the way the scroll is
// going, the new one arrives from the opposite edge. No scaling at any point.
function stepTransition(now){
 const tr=transition,t=clamp(now-tr.start,0,DURATION),dir=tr.forward?-1:1;
 if(t<OUT_END){
  const u=smooth(t/OUT_END);slideFeature(tr.outEl,dir*tr.shift*u,1-u);
 }else{
  if(!tr.snapped){tr.snapped=true;snap();slideFeature(tr.outEl,0,0);}
  const u=smooth(clamp((t-IN_START)/(IN_END-IN_START)));
  slideFeature(tr.inEl,-dir*tr.shift*(1-u),u);
 }
 document.body.dataset.phase=t<OUT_END?'exit':t<IN_START?'travel':'enter';
 if(t>=DURATION)finish();
}

// Full-screen pulse and quiet idle heartbeat have completely separate clocks.
// The diagonal is r+c=cycle; only active diagonal cells are painted.
function drawPulse(ctx,t,amp,forward,area){
 // Optional local bounds let navigation reuse this exact diagonal wavefront.
 const cell=area?area.cell:30,cols=Math.ceil((area?area.width:W)/cell),rows=Math.ceil((area?area.height:H)/cell),period=cols+rows+9;
 const head=(forward?t:1-t)*period-4;
 const width=Math.max(3.6,period*.05),echoGap=Math.max(7,period*.10),reach=Math.ceil(width+echoGap);
 const envelope=Math.min(1,t*12,(1-t)*12)*amp;
 for(let r=0;r<rows;r++){
  const lo=Math.max(0,Math.floor(head-r-reach)),hi=Math.min(cols,Math.ceil(head-r+reach));
  for(let col=lo;col<hi;col++){
   const diag=r+col,dist=Math.abs(diag-head),echo=Math.abs(diag-(head+(forward?-echoGap:echoGap)));
   const glow=Math.max(0,1-dist/width,(1-echo/(width*.65))*.32)*envelope;if(glow<.012)continue;
   const scale=cell/30,size=(amp>.5?22:17)*scale,x=col*cell+cell/2,y=r*cell+cell/2;
   ctx.globalAlpha=glow*.085;ctx.fillStyle=area?area.tint:'#e8963d';ctx.fillRect(x-16*scale,y-16*scale,32*scale,32*scale);
   ctx.globalAlpha=glow*.90;ctx.fillStyle=area?area.tint:dist<1.3?'#f2c18b':'#d88e44';ctx.fillRect(x-size/2,y-size/2,size,size);
  }
 }
 ctx.globalAlpha=1;
}
// Bounds are cached at layout changes, never measured in the animation loop.
function resizeNavMatrix(){
 if(!navCtx)return;
 const rect=nav.getBoundingClientRect(),mobile=getComputedStyle(nav).flexDirection==='row',dpr=Math.min(devicePixelRatio||1,1.5);
 navWidth=rect.width;navHeight=rect.height;
 const width=Math.max(1,Math.round(navWidth*dpr)),height=Math.max(1,Math.round(navHeight*dpr));
 if(navCanvas.width!==width||navCanvas.height!==height){navCanvas.width=width;navCanvas.height=height;}
 navCtx.setTransform(dpr,0,0,dpr,0,0);
 navFields=buttons.map(b=>{
  const r=b.getBoundingClientRect(),cell=mobile?Math.min(10,r.width/3,r.height/3):Math.min(r.height/3,clamp(parseFloat(getComputedStyle(b).fontSize),12,18));
  const cols=mobile?3:Math.max(1,Math.floor(r.width/cell)),rows=3;
  return {x:mobile?r.left-rect.left+(r.width-cols*cell)/2:r.right-rect.left-cols*cell,y:r.top-rect.top+(r.height-cell*rows)/2,width:cols*cell,height:cell*rows,cell,cols,rows,tint:''};
 });
 lastBg=0;ensureFrame();
}
function drawNavMatrix(now){
 if(!navCtx||!navFields.length)return;
 navCtx.clearRect(0,0,navWidth,navHeight);
 const dt=Math.min(80,Math.max(0,now-(navTime||now)));navTime=now;
 navFields.forEach((field,i)=>{
  const state=navStates[i],warm=i===current||i===navHover||i===navFocus;
  state.heat=motion.matches?Number(warm):mix(state.heat,Number(warm),1-Math.exp(-dt/85));
  field.tint='rgb('+COOL.map((c,k)=>Math.round(mix(c,WARM[k],state.heat)*255)).join(',')+')';
  navCtx.save();navCtx.translate(field.x,field.y);
  navCtx.beginPath();navCtx.rect(0,0,field.width,field.height);navCtx.clip();
  navCtx.fillStyle=field.tint;
  // Sparse quiet cells keep the array present between pulses.
  for(let row=0;row<field.rows;row++)for(let col=0;col<field.cols;col++){
   if((col+row*3+i)%4>1)continue;
   const size=field.cell*17/30,inset=(field.cell-size)/2;
   navCtx.globalAlpha=.075+state.heat*.045;
   navCtx.fillRect(col*field.cell+inset,row*field.cell+inset,size,size);
  }
  navCtx.globalAlpha=1;
  if(!motion.matches){
   const age=now-state.kick,engaged=age>=0&&age<820;
   const t=transition&&i===current?clamp((now-transition.start)/DURATION):engaged?age/820:((now+i*430)%3200)/3200;
   drawPulse(navCtx,t,engaged ? .56 : .32+state.heat*.12,true,field);
  }
  navCtx.restore();
 });
}
function wakeNavMatrix(i){
 navStates[i].kick=performance.now();lastBg=0;ensureFrame();
}
function makeGlowSprite(){
 glowSprite=document.createElement('canvas');glowSprite.width=glowSprite.height=320;
 const g=glowSprite.getContext('2d'),light=g.createRadialGradient(160,160,0,160,160,160);
 light.addColorStop(0,'rgba(232,150,61,.30)');light.addColorStop(.3,'rgba(232,150,61,.18)');
 light.addColorStop(.7,'rgba(95,160,201,.055)');light.addColorStop(1,'rgba(95,160,201,0)');
 g.fillStyle=light;g.fillRect(0,0,320,320);
}
function buildMatrix(){
 matrixBase=document.createElement('canvas');const dpr=overlayDpr;
 matrixBase.width=Math.round(W*dpr);matrixBase.height=Math.round(H*dpr);
 const ctx=matrixBase.getContext('2d');ctx.setTransform(dpr,0,0,dpr,0,0);
 const cols=Math.ceil(W/30),rows=Math.ceil(H/30);
 ctx.beginPath();for(let r=0;r<rows;r++)for(let c=0;c<cols;c++)ctx.rect(c*30+5.5,r*30+5.5,19,19);
 ctx.strokeStyle='rgba(140,153,166,.055)';ctx.lineWidth=.7;ctx.stroke();
 // A fixed scatter of cells with no clocks of their own. A wave crossing one
 // ignites it; it then fades, so the sparkle is the wave's wake.
 const count=Math.min(cols*rows,64,Math.max(22,Math.floor(cols*rows*.035)));
 let seed=18371;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
 matrixCells=[];const used=new Set();
 for(let i=0;i<count;i++){
  let index;do{index=Math.floor(random()*cols*rows);}while(used.has(index));used.add(index);
  matrixCells.push({x:index%cols*30+6,y:Math.floor(index/cols)*30+6,alpha:.16+random()*.10});
 }
 cellGlow=new Float32Array(matrixCells.length);
}
function drawOverlay(now,sweep){
 const power=pointerPower(now)/POINTER_POWER;
 bgc.clearRect(0,0,W,H);
 bgc.drawImage(matrixBase,0,0,W,H);
 activeCells.length=0;
 if(!motion.matches&&cellGlow){
  // Half-life 900ms, clamped against a long frame gap so a backgrounded tab
  // does not come back with everything still lit.
  const dt=clamp(now-(lastOverlay||now),0,80),decay=Math.pow(.5,dt/900);
  lastOverlay=now;bgc.fillStyle='#9caab4';
  for(let i=0;i<matrixCells.length;i++){
   const cell=matrixCells[i],x=cell.x+9,y=cell.y+9;
   let g=cellGlow[i]*decay;
   if(sweep&&sweep.kind!=='warp'){
    const reach=sweep.width*.8,d=Math.abs(x+y-sweep.head);
    if(d<reach)g=Math.max(g,(1-d/reach)**2);
   }
   cellGlow[i]=g;
   if(g<=.02)continue;
   bgc.globalAlpha=Math.min(.6,g*cell.alpha*2);bgc.fillRect(cell.x,cell.y,18,18);
   if(g>.07)activeCells.push({x:cell.x,y:cell.y,e:g});
  }
  bgc.globalAlpha=1;
 }
 // A page turn gets its diagonal wavefront. A dive gets nothing here on
 // purpose: the 2D overlay is what the fabric is read *through*, so anything
 // drawn on it during a close-up competes with the very geometry the flight
 // exists to show.
 if(sweep&&sweep.kind!=='warp')drawPulse(bgc,sweep.t,sweep.amp,sweep.forward);
 if(pointer&&power>0){
  bgc.globalAlpha=power;bgc.drawImage(glowSprite,pointer.x-160,pointer.y-160);
  const col=Math.floor(pointer.x/30),row=Math.floor(pointer.y/30);
  for(let r=Math.max(0,row-4);r<=row+4;r++)for(let c=Math.max(0,col-4);c<=col+4;c++){
   const x=c*30+15,y=r*30+15,d=Math.hypot(x-pointer.x,y-pointer.y),light=Math.max(0,1-d/125);
   if(!light)continue;
   bgc.globalAlpha=light*light*.62*power;bgc.fillStyle='#e8a052';bgc.fillRect(x-9,y-9,18,18);
  }
  bgc.globalAlpha=1;
 }
}
function drawScene(now){
 const sweep=sceneSweep(now),pulses=scenePulses(now);
 document.body.dataset.heartbeat=transition?'navigating':pulses?'flowing':'off';
 drawOverlay(now,sweep);drawNavMatrix(now);
 const reveal=revealAmount(now);
 const exposure=AMBIENT+REVEAL*reveal+DIVE_EXPOSURE*zoomAmount(now);
 if(renderer&&!renderFailed)renderer.render(cameraPose(now),now,sceneLights(now),sweep,exposure,pulses);
}
function frame(now){
 raf=0;if(document.hidden)return;
 if(transition)stepTransition(now);
 if(zoom)stepZoom(now);
 publishZoom(now);
 const budget=transition||zoom?0:(now-pointerStamp<120?12:W<=900?48:32);
 if(motion.matches||now-lastBg>=budget){drawScene(now);lastBg=now;}
 // An open close-up holds the exposure at full, so it cannot be what keeps
 // the loop alive — otherwise reduced motion would never come to rest.
 if(transition||zoom||!motion.matches||(!detail&&revealAmount(now)>0)||pointerPower(now)>0)ensureFrame();
}
function ensureFrame(){if(!raf&&!document.hidden)raf=requestAnimationFrame(frame);}
function resize(){
 W=innerWidth;H=innerHeight;const dpr=overlayDpr=Math.min(devicePixelRatio||1,1.5,Math.sqrt(3600000/Math.max(1,W*H)));
 bg.width=Math.round(W*dpr);bg.height=Math.round(H*dpr);bgc.setTransform(dpr,0,0,dpr,0,0);
 if(renderer)renderer.resize();buildMatrix();resizeNavMatrix();
 if(transition&&!transition.snapped)window.scrollTo(0,sections[transition.from].offsetTop);else snap();
 lastBg=0;ensureFrame();
}
function editable(el){return el&&!!el.closest('input,textarea,select,[contenteditable="true"],a,button');}
function atEdge(down){const s=sections[current];return down?s.scrollHeight-s.scrollTop-s.clientHeight<2:s.scrollTop<2;}
window.addEventListener('wheel',e=>{
 if(e.ctrlKey)return; // Preserve browser pinch-to-zoom.
 if(zoom||detail)return; // The open close-up scrolls itself.
 const now=performance.now(),gap=now-lastWheel;lastWheel=now;
 if(transition){e.preventDefault();wheelSum=0;return;}
 if(Math.abs(e.deltaY)<=Math.abs(e.deltaX))return;
 const down=e.deltaY>0;if(!atEdge(down)){wheelSum=0;return;}e.preventDefault();
 if(now-lastEnd<320||gap<140&&now-lastEnd<750)return;
 let delta=e.deltaY*(e.deltaMode===1?16:e.deltaMode===2?H:1);
 if(now-wheelTime>180||Math.sign(delta)!==Math.sign(wheelSum))wheelSum=0;wheelTime=now;wheelSum+=delta;
 if(Math.abs(wheelSum)>=45){go(current+(down?1:-1));wheelSum=0;}
},{passive:false});
window.addEventListener('touchstart',e=>{
 if(zoom||detail){touch=null;return;}
 if(e.touches.length!==1){touch=null;return;}const t=e.touches[0];touch={x:t.clientX,y:t.clientY,scroll:sections[current].scrollTop,edgeUp:atEdge(false),edgeDown:atEdge(true),blocked:!!transition};
},{passive:true});
window.addEventListener('touchmove',e=>{
 if(zoom||detail)return;
 if(e.touches.length!==1){touch=null;return;}if(!touch)return;
 const d=touch.y-e.touches[0].clientY;if(transition||(Math.abs(d)>8&&atEdge(d>0)))e.preventDefault();
},{passive:false});
window.addEventListener('touchend',e=>{
 if(!touch)return;const t=touch;touch=null;if(transition||zoom||detail||t.blocked)return;
 const dy=t.y-e.changedTouches[0].clientY,dx=t.x-e.changedTouches[0].clientX;
 if(Math.abs(dy)<55||Math.abs(dy)<Math.abs(dx)||Math.abs(sections[current].scrollTop-t.scroll)>3)return;
 if(dy>0?t.edgeDown:t.edgeUp)go(current+(dy>0?1:-1));
},{passive:true});
window.addEventListener('touchcancel',()=>touch=null,{passive:true});
// Touch devices have no hover, so the finger carries the halo that a mouse
// would. Registered separately from the swipe handlers above so the two
// concerns stay independent.
function carryLight(e,holding){
 const t=(e.touches&&e.touches[0])||(e.changedTouches&&e.changedTouches[0]);
 if(!t)return;
 pointer={x:t.clientX,y:t.clientY,touch:true};
 touchHold=holding;if(!holding)touchRelease=performance.now();
 pointerStamp=performance.now();lastBg=0;ensureFrame();
}
window.addEventListener('touchstart',e=>carryLight(e,true),{passive:true});
window.addEventListener('touchmove',e=>carryLight(e,true),{passive:true});
window.addEventListener('touchend',e=>carryLight(e,false),{passive:true});
window.addEventListener('touchcancel',e=>carryLight(e,false),{passive:true});
window.addEventListener('keydown',e=>{
 if(e.key==='Escape'&&(zoom||detail)){e.preventDefault();if(detail)closeDetail();return;}
 if(zoom||detail)return;
 if(e.key==='Escape'&&transition){e.preventDefault();finish();return;}
 if(editable(e.target))return;
 const down=['ArrowDown','PageDown',' '].includes(e.key)&&!e.shiftKey,up=['ArrowUp','PageUp'].includes(e.key)||(e.key===' '&&e.shiftKey);
 if(!down&&!up&&!['Home','End'].includes(e.key))return;e.preventDefault();if(transition||e.repeat)return;
 if(e.key==='Home'){go(0);return;}if(e.key==='End'){go(sections.length-1);return;}
 if(!atEdge(down)){sections[current].scrollBy({top:(down?1:-1)*(e.key.startsWith('Arrow')?70:H*.7),behavior:motion.matches?'instant':'smooth'});return;}
 go(current+(down?1:-1));
});
buttons.forEach((b,i)=>{
 b.addEventListener('click',()=>{
  wakeNavMatrix(i);
  if(zoom)return; // mid-flight: let it land first
  if(detail){closeDetail(null,i);return;}
  go(i);
 });
 b.addEventListener('pointerenter',e=>{if(e.pointerType!=='touch'){navHover=i;wakeNavMatrix(i);}});
 b.addEventListener('pointerleave',()=>{if(navHover===i)navHover=-1;lastBg=0;ensureFrame();});
 b.addEventListener('focus',()=>{navFocus=i;wakeNavMatrix(i);});
 b.addEventListener('blur',()=>{if(navFocus===i)navFocus=-1;lastBg=0;ensureFrame();});
});
if(typeof ResizeObserver!=='undefined')new ResizeObserver(resizeNavMatrix).observe(nav);
else if(document.fonts)document.fonts.ready.then(resizeNavMatrix);
window.addEventListener('hashchange',()=>{if(zoom||detail)return;const i=sections.findIndex(s=>s.id===location.hash.slice(1));if(i>=0){if(transition)finish();go(i,false);}});
function queueResize(){
 if(!resizeFrame)resizeFrame=requestAnimationFrame(()=>{resizeFrame=0;resize();});
}
window.addEventListener('resize',queueResize,{passive:true});
document.addEventListener('visibilitychange',()=>{if(document.hidden){if(raf)cancelAnimationFrame(raf);raf=0;if(transition)finish();}else{lastBg=0;ensureFrame();}});
motion.addEventListener('change',()=>{if(transition)finish();if(motion.matches){bgc.clearRect(0,0,W,H);document.body.dataset.heartbeat='off';}ensureFrame();});
window.addEventListener('pointermove',e=>{if(e.pointerType==='mouse'){pointer={x:e.clientX,y:e.clientY};pointerStamp=performance.now();ensureFrame();}},{passive:true});
document.addEventListener('pointerleave',()=>{pointer=null;lastBg=0;ensureFrame();});

// Existing homepage interactions.
function copyText(text){
 if(navigator.clipboard&&isSecureContext)return navigator.clipboard.writeText(text);
 const ta=document.createElement('textarea');ta.value=text;ta.style.cssText='position:fixed;opacity:0';document.body.appendChild(ta);ta.select();const copied=document.execCommand('copy');ta.remove();return copied?Promise.resolve():Promise.reject(Error('copy'));
}
document.querySelectorAll('.contact-icon[data-copy]').forEach(b=>b.addEventListener('click',()=>{
 copyText(b.dataset.copy).then(()=>{const tip=b.querySelector('.copied-tip');tip.textContent='Copied!';tip.classList.add('show');setTimeout(()=>tip.classList.remove('show'),1200);}).catch(()=>{const tip=b.querySelector('.copied-tip');tip.textContent=b.dataset.copy;tip.classList.add('show');});
}));
// ---- entry close-ups ------------------------------------------------------
// Inspect flies the camera from the district a section is parked on down onto
// the single component that entry is filed under; the page copy steps aside on
// the way, and the entry's long form is read against that close-up. Zoom out
// runs exactly the same flight backwards.
const root=document.documentElement;
const detailLayer=$('#detailLayer');
const detailTitle=$('#detailTitle'),detailMeta=$('#detailMeta'),detailBody=$('#detailBody');
const detailLinks=$('#detailLinks'),detailClose=$('#detailClose');
// An entry with no named focus dives straight down onto its own district.
function fallbackFocus(){
 const b=poses[current];
 return {target:[b.target[0],b.target[1]+.25,b.target[2]],dist:b.dist*.32,phi:b.phi,theta:b.theta+.22,fov:.47};
}
function instant(){return motion.matches||!renderer||renderFailed;}
function openDetail(trigger){
 if(zoom||detail||transition)return;
 const entry=trigger.closest('.role,.project'),src=entry&&entry.querySelector('.entry-detail');
 if(!src)return;
 const pose=focusPoses[entry.dataset.focus]||fallbackFocus();
 const heading=entry.querySelector('.role-title,.project-title');
 detailTitle.textContent=trigger.dataset.title||(heading?heading.textContent.trim():'');
 detailMeta.textContent=trigger.dataset.meta||'';
 detailBody.innerHTML=src.innerHTML;
 // Links belong beside the title, as icons: appendChild moves each one out of
 // the body it was authored in, and its label survives as the accessible name.
 detailLinks.replaceChildren();
 detailBody.querySelectorAll('.detail-link').forEach(a=>{
  const label=a.querySelector('span');
  if(label){a.setAttribute('aria-label',label.textContent.trim());a.title=label.textContent.trim();label.remove();}
  detailLinks.appendChild(a);
 });
 detailBody.scrollTop=0;detailLayer.hidden=false;
 // The rail stays live while a close-up is open — only the copy behind the
 // panel goes inert, so nothing invisible can be tabbed into.
 sections[current].inert=true;sections[current].setAttribute('aria-hidden','true');
 root.classList.add('detail-open');
 document.body.dataset.heartbeat='off';
 if(instant()){detail={entry,pose,trigger};showPanel();lastBg=0;ensureFrame();return;}
 zoom={dir:'in',start:performance.now(),span:ZOOM_IN,pose,entry,trigger};
 publishZoom(zoom.start);lastBg=0;ensureFrame();
}
function showPanel(){
 detailLayer.classList.add('is-open');
 publishZoom(performance.now());
 document.body.dataset.phase='detail';
 // The body is the scroll container, so focusing it (not the button) is what
 // lets a keyboard read the long form.
 (detailBody||detailClose).focus({preventScroll:true});
}
// `to` is a section the rail has asked for. The flight out is then aimed at
// *that* section's district instead of at the one the close-up was opened
// from, so leaving for somewhere else is a single move — not a flight home
// followed by a second flight across, which is two of them back to back.
function closeDetail(then,to){
 if(!detail||zoom)return;
 const d=detail;detail=null;
 detailLayer.classList.remove('is-open');
 let span=ZOOM_OUT;
 if(to!==undefined&&to!==current&&to>=0&&to<sections.length){
  const hops=Math.abs(to-current);
  current=to;
  history.replaceState(null,'','#'+sections[current].id);
  // The rail and the progress bar answer the click at once; the copy behind
  // the panel is still fully dissolved, so the page can be scrolled under it
  // without anything being seen to jump.
  labels();
  sections[current].inert=true;sections[current].setAttribute('aria-hidden','true');
  snap();
  // Districts are 10 units apart, so a far hand-off is a much longer trip
  // than a plain zoom out. Without this the distant ones arrive at a sprint.
  span+=Math.min(700,hops*190);
  then=()=>sections[current].focus({preventScroll:true});
 }
 if(instant()){surface(d.trigger,then);return;}
 zoom={dir:'out',start:performance.now(),span,pose:d.pose,entry:d.entry,trigger:d.trigger,then};
 publishZoom(zoom.start);lastBg=0;ensureFrame();
}
function surface(trigger,then){
 root.classList.remove('detail-open');
 detailLayer.hidden=true;
 publishZoom(performance.now());
 labels(); // restores each section's own inert state
 document.body.dataset.phase='content';
 document.body.dataset.heartbeat=motion.matches?'off':'waiting';
 lastEnd=performance.now();lastBg=0;ensureFrame();
 // A hand-off moves focus itself; only a plain close returns it to the entry.
 if(then)then();else if(trigger)trigger.focus({preventScroll:true});
}
function stepZoom(now){
 const z=zoom,span=z.span,t=now-z.start;
 document.body.dataset.phase=z.dir==='in'?'dive':'surface';
 // Nothing is handed back part-way through any more: the copy comes home on
 // the same ramp the camera is on, so the flight is one move in both
 // directions instead of a flight followed by a hand-off.
 if(t<span)return;
 zoom=null;
 if(z.dir==='in'){detail={entry:z.entry,pose:z.pose,trigger:z.trigger};showPanel();lastBg=0;ensureFrame();}
 else surface(z.trigger,z.then);
}
document.querySelectorAll('.entry-more').forEach(b=>b.addEventListener('click',()=>openDetail(b)));
// The whole entry is the hit area. Links and the control itself keep their own
// behaviour, and a click that ends a text selection is a selection, not a dive.
document.querySelectorAll('.role,.project').forEach(entry=>{
 const button=entry.querySelector('.entry-more');
 if(!button||!entry.querySelector('.entry-detail'))return;
 entry.classList.add('is-inspectable');
 let downX=0,downY=0;
 entry.addEventListener('pointerdown',e=>{downX=e.clientX;downY=e.clientY;},{passive:true});
 entry.addEventListener('click',e=>{
  if(e.target.closest('a,button,input,textarea,select'))return;
  if(Math.hypot(e.clientX-downX,e.clientY-downY)>10)return; // a drag, not a tap
  const picked=getSelection&&getSelection();
  if(picked&&!picked.isCollapsed&&picked.toString().trim())return;
  openDetail(button);
 });
});
if(detailClose)detailClose.addEventListener('click',()=>closeDetail());

sections.forEach(s=>s.tabIndex=-1);
try{renderer=createPackage($('#packageCanvas'));}catch(e){renderFailed=true;console.warn('Compute renderer unavailable; using direct section navigation.',e);}
// Warm the shader before the first frame so the fabric is there on load.
if(renderer&&!renderFailed)renderer.render(cameraPose(performance.now()),0,[],null,AMBIENT,null);
document.documentElement.classList.add('enhanced');if('scrollRestoration'in history)history.scrollRestoration='manual';
makeGlowSprite();labels();resize();document.body.dataset.phase='content';document.body.dataset.heartbeat=motion.matches?'off':'waiting';
})();
