#include <QApplication>
#include <QWidget>
#include <QVBoxLayout>
#include <QScrollArea>
#include <QScrollBar>
#include <QKeyEvent>
#include <QMouseEvent>
#include <QContextMenuEvent>
#include <QMenu>
#include <QAction>
#include <QClipboard>
#include <QFontMetrics>
#include <QPainter>
#include <QTimer>
#include <QSocketNotifier>
#include <QColor>
#include <QScreen>
#include <QFile>
#include <QJsonDocument>
#include <QJsonObject>
#include <QDir>
#include <QPropertyAnimation>
#include <QGraphicsOpacityEffect>
#include <QSlider>
#include <QCheckBox>
#include <QLabel>
#include <QHBoxLayout>
#include <QLinearGradient>
#include <QRegularExpression>
#include <QPainterPath>
#include <QPushButton>
#include <QColorDialog>

#include <cmath>

#include <pty.h>
#include <unistd.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <signal.h>
#include <fcntl.h>
#include <string.h>

// ── ANSI colour tables ────────────────────────────────────────────────────────
static const QColor ansi16[16] = {
    {  12, 12, 12},{197, 15, 31},{19,161, 14},{193,156, 0},
    {  0,55,218},{136, 23,152},{58,150,221},{204,204,204},
    {118,118,118},{231, 72, 86},{22,198, 12},{249,241,165},
    { 59,120,255},{180,  0,158},{97,214,214},{242,242,242}
};
static QColor ansiColor(int n){
    if(n<16)  return ansi16[n];
    if(n<232){
        n-=16;
        int b=n%6, g=(n/6)%6, r=n/36;
        auto c=[](int v){return v?55+v*40:0;};
        return {c(r),c(g),c(b)};
    }
    int v=8+(n-232)*10;
    return {v,v,v};
}

// ── Cell ─────────────────────────────────────────────────────────────────────
struct Attr {
    QColor fg{204,204,204}, bg{0,0,0};
    bool bold=false, underline=false, italic=false, reverse=false;
};
struct Cell { QChar ch{' '}; Attr attr; };

// ── Screen buffer ─────────────────────────────────────────────────────────────
class Screen {
public:
    int cols, rows;
    int cx=0, cy=0;
    bool cursorVisible=true;
    QVector<QVector<Cell>> lines;
    QVector<QVector<Cell>> scrollback;
    // Monotonically counts every line ever pushed into scrollback, even
    // once the 5000-line cap starts evicting the oldest to make room. Used
    // instead of scrollback.size() to detect "how much new output arrived"
    // — once the cap is active, appending a line ALSO evicts one, so
    // scrollback.size()'s net delta is 0 even though real content was
    // produced. See TermWidget::onData(), which needs the true count to
    // keep the user's scroll position pinned to the same conceptual lines
    // instead of quietly drifting forward as old lines get evicted.
    long long totalScrolledLines=0;
    Attr curAttr;
    bool wrapNext=false;

    // saved cursor
    int sx=0, sy=0;
    Attr sattr;

    // selection
    int selStartX=-1,selStartY=-1,selEndX=-1,selEndY=-1;

    Screen(int c,int r): cols(c),rows(r){
        lines.resize(r);
        for(auto &l:lines) l.resize(c);
    }

    void resize(int c,int r){
        cols=c; rows=r;
        lines.resize(r);
        for(auto &l:lines){
            l.resize(c);
        }
        cx=qMin(cx,c-1);
        cy=qMin(cy,r-1);
    }

    Cell &at(int x,int y){ return lines[y][x]; }

    void scrollUp(int top,int bot){
        if(top>=bot) return;
        scrollback.append(lines[top]);
        totalScrolledLines++;
        if(scrollback.size()>5000) scrollback.removeFirst();
        lines.removeAt(top);
        QVector<Cell> blank(cols);
        lines.insert(bot,blank);
    }

    void scrollDown(int top,int bot){
        lines.removeAt(bot);
        QVector<Cell> blank(cols);
        lines.insert(top,blank);
    }

    void clearLine(int y,int x1,int x2){
        for(int x=x1;x<=x2&&x<cols;x++)
            lines[y][x]={' ',curAttr};
    }

    void eraseLine(int y){ clearLine(y,0,cols-1); }

    // alternate screen buffer (for TUI apps like fastfetch, vim, etc.)
    QVector<QVector<Cell>> altLines;
    int altCx=0, altCy=0;
    Attr altAttr;
    bool altActive=false;

    void switchToAlt(){
        if(altActive) return;
        altActive=true;
        altLines=lines;
        altCx=cx; altCy=cy; altAttr=curAttr;
        // clear main screen for alt buffer
        lines.clear();
        lines.resize(rows);
        for(auto &l:lines) l.resize(cols);
        cx=0; cy=0; curAttr=Attr{};
    }

    void switchToNormal(){
        if(!altActive) return;
        altActive=false;
        lines=altLines;
        cx=altCx; cy=altCy; curAttr=altAttr;
        altLines.clear();
    }

    QString selectedText() const {
        if(selStartY<0) return {};
        int ay=selStartY,ax=selStartX,by=selEndY,bx=selEndX;
        if(ay>by||(ay==by&&ax>bx)){qSwap(ay,by);qSwap(ax,bx);}
        // map into scrollback+lines
        int sb=scrollback.size();
        QString out;
        for(int y=ay;y<=by;y++){
            int x0=(y==ay?ax:0), x1=(y==by?bx:cols-1);
            const QVector<Cell>*row=nullptr;
            if(y<sb) row=&scrollback[y];
            else if(y-sb<lines.size()) row=&lines[y-sb];
            if(!row) continue;
            for(int x=x0;x<=x1&&x<row->size();x++)
                out+=(*row)[x].ch;
            if(y<by) out+='\n';
        }
        return out.trimmed();
    }
};

// DEC Special Graphics charset (VT100 "0" designation) — maps the ASCII
// bytes 0x60-0x7e to the line-drawing/shading glyphs ncurses apps (vim,
// nano, etc.) draw borders with when they switch into it via ESC(0 / ESC)0
// or shift into G1 via SO. Without this, those bytes print as their literal
// ASCII letters — a repeated 'a' (checkerboard/shading) looks like a brick
// wall, and the box-corner letters (l,k,m,j,q,x,t,u,v,w,n) look like
// scattered symbols instead of a drawn border.
static QChar acsTranslate(unsigned char c){
    switch(c){
    case 0x60: return QChar(0x25C6); // ` diamond
    case 0x61: return QChar(0x2592); // a checkerboard/shading
    case 0x62: return QChar(0x2409); // b HT symbol
    case 0x63: return QChar(0x240C); // c FF symbol
    case 0x64: return QChar(0x240D); // d CR symbol
    case 0x65: return QChar(0x240A); // e LF symbol
    case 0x66: return QChar(0x00B0); // f degree
    case 0x67: return QChar(0x00B1); // g plus/minus
    case 0x68: return QChar(0x2424); // h NL symbol
    case 0x69: return QChar(0x240B); // i VT symbol
    case 0x6A: return QChar(0x2518); // j bottom-right corner
    case 0x6B: return QChar(0x2510); // k top-right corner
    case 0x6C: return QChar(0x250C); // l top-left corner
    case 0x6D: return QChar(0x2514); // m bottom-left corner
    case 0x6E: return QChar(0x253C); // n crossing lines
    case 0x6F: return QChar(0x23BA); // o scan line 1
    case 0x70: return QChar(0x23BB); // p scan line 3
    case 0x71: return QChar(0x2500); // q horizontal line
    case 0x72: return QChar(0x23BC); // r scan line 7
    case 0x73: return QChar(0x23BD); // s scan line 9
    case 0x74: return QChar(0x251C); // t left tee
    case 0x75: return QChar(0x2524); // u right tee
    case 0x76: return QChar(0x2534); // v bottom tee
    case 0x77: return QChar(0x252C); // w top tee
    case 0x78: return QChar(0x2502); // x vertical line
    case 0x79: return QChar(0x2264); // y less-or-equal
    case 0x7A: return QChar(0x2265); // z greater-or-equal
    case 0x7B: return QChar(0x03C0); // { pi
    case 0x7C: return QChar(0x2260); // | not-equal
    case 0x7D: return QChar(0x00A3); // } pound sterling
    case 0x7E: return QChar(0x00B7); // ~ centered dot
    default:   return QChar(c);
    }
}

// ── VT Parser ─────────────────────────────────────────────────────────────────
class VTParser : public QObject {
    Q_OBJECT
public:
    Screen *scr;
    int scrollTop=0, scrollBot;
    QByteArray buf;
    int master=-1;

    // Charset state: which glyph set G0/G1 currently designate ('B' = ASCII,
    // '0' = DEC Special Graphics), and whether SO (Shift Out, 0x0E) has
    // switched active output to G1 (SI, 0x0F, switches back to G0).
    char g0charset='B', g1charset='B';
    bool shiftedToG1=false;

    VTParser(Screen *s):scr(s),scrollBot(s->rows-1){}

    void feed(const QByteArray &data){
        buf+=data;
        parse();
    }

private:
    void parse(){
        int i=0;
        while(i<buf.size()){
            unsigned char c=buf[i];
            if(c==0x1b){
                if(i+1>=buf.size()) break;
                char next=buf[i+1];
                if(next=='['){
                    // CSI
                    int j=i+2;
                    while(j<buf.size()&&(buf[j]<0x40||buf[j]>0x7e)) j++;
                    if(j>=buf.size()) break;
                    QByteArray seq=buf.mid(i+2,j-(i+2));
                    char cmd=buf[j];
                    csi(seq,cmd);
                    i=j+1;
                } else if(next==']'){
                    // OSC — skip to BEL or ST
                    int j=i+2;
                    while(j<buf.size()&&buf[j]!=0x07&&
                          !(j+1<buf.size()&&buf[j]==0x1b&&buf[j+1]=='\\')) j++;
                    if(j>=buf.size()) break;
                    i=j+1;
                    if(i<buf.size()&&buf[i-1]==0x1b) i++;
                } else if(next=='P'||next=='X'||next=='^'||next=='_'){
                    // DCS / SOS / PM / APC — all string-terminated the same
                    // way as OSC (BEL or ST). Previously unhandled: fell
                    // through to esc(next), which only consumes ESC+next
                    // and leaves the whole payload to be printed as regular
                    // characters — garbage on screen for any app that emits
                    // one (some shells probe terminal capabilities via DCS).
                    int j=i+2;
                    while(j<buf.size()&&buf[j]!=0x07&&
                          !(j+1<buf.size()&&buf[j]==0x1b&&buf[j+1]=='\\')) j++;
                    if(j>=buf.size()) break;
                    i=j+1;
                    if(i<buf.size()&&buf[i-1]==0x1b) i++;
                } else if(next=='('||next==')'){
                    // Charset designation for G0 ('(') or G1 (')'). Need the
                    // third byte (the charset id, e.g. '0' for DEC Special
                    // Graphics, 'B' for plain ASCII) — wait for more data
                    // rather than guessing if it hasn't arrived yet.
                    if(i+2>=buf.size()) break;
                    char id=buf[i+2];
                    if(next=='(') g0charset=id; else g1charset=id;
                    i+=3;
                } else {
                    esc(next); i+=2;
                }
            } else if(c=='\r'){
                scr->cx=0; i++;
            } else if(c=='\n'||c==0x0b||c==0x0c){
                linefeed(); i++;
            } else if(c=='\t'){
                scr->cx=((scr->cx/8)+1)*8;
                if(scr->cx>=scr->cols) scr->cx=scr->cols-1;
                i++;
            } else if(c==0x08){
                if(scr->cx>0) scr->cx--; i++;
            } else if(c==0x07){
                i++; // bell ignore
            } else if(c==0x0e){
                shiftedToG1=true; i++;  // SO — switch active charset to G1
            } else if(c==0x0f){
                shiftedToG1=false; i++; // SI — switch active charset to G0
            } else if(c>=0x80){
                // UTF-8 multibyte
                int seqLen=0;
                if((c&0xE0)==0xC0) seqLen=2;
                else if((c&0xF0)==0xE0) seqLen=3;
                else if((c&0xF8)==0xF0) seqLen=4;
                else { i++; continue; }
                if(i+seqLen>buf.size()) break;
                QString s=QString::fromUtf8(buf.constData()+i,seqLen);
                // filter fish "no newline" marker U+23CE ⏎
                if(!s.isEmpty() && s[0].unicode() != 0x23CE) putChar(s[0]);
                i+=seqLen;
            } else if(c>=0x20){
                putChar(QChar(c)); i++;
            } else { i++; }
        }
        buf=buf.mid(i);
    }

    void linefeed(){
        scr->wrapNext=false;
        if(scr->cy==scrollBot) scr->scrollUp(scrollTop,scrollBot);
        else scr->cy=qMin(scr->cy+1,scr->rows-1);
    }

    void putChar(QChar ch){
        // Translate through the DEC Special Graphics table when the
        // currently-active charset (G1 if shifted out via SO, else G0) is
        // designated '0'. Only single-byte bytes in 0x60-0x7e are ever
        // remapped by real VT100s — anything else (including all UTF-8
        // multibyte input, which never lands here as a raw 0x60-0x7e byte)
        // passes through untouched.
        char active=shiftedToG1?g1charset:g0charset;
        if(active=='0'&&ch.unicode()>=0x60&&ch.unicode()<=0x7e){
            ch=acsTranslate((unsigned char)ch.unicode());
        }
        if(scr->wrapNext){
            scr->cx=0;
            linefeed();
            scr->wrapNext=false;
        }
        if(scr->cx<scr->cols&&scr->cy<scr->rows)
            scr->at(scr->cx,scr->cy)={ch,scr->curAttr};
        if(scr->cx+1>=scr->cols) scr->wrapNext=true;
        else scr->cx++;
    }

    QList<int> params(const QByteArray &seq){
        QList<int> p;
        for(auto &s:seq.split(';'))
            p.append(s.isEmpty()?0:s.toInt());
        if(p.isEmpty()) p.append(0);
        return p;
    }

    void csi(const QByteArray &seq, char cmd){
        auto p=params(seq);
        auto P=[&](int i,int def=0){return i<p.size()?p[i]:def;};
        switch(cmd){
        case 'A': scr->cy=qMax(0,scr->cy-qMax(1,P(0))); break;
        case 'B': scr->cy=qMin(scr->rows-1,scr->cy+qMax(1,P(0))); break;
        case 'C': scr->cx=qMin(scr->cols-1,scr->cx+qMax(1,P(0))); break;
        case 'D': scr->cx=qMax(0,scr->cx-qMax(1,P(0))); break;
        case 'E': scr->cy=qMin(scr->rows-1,scr->cy+qMax(1,P(0))); scr->cx=0; break;
        case 'F': scr->cy=qMax(0,scr->cy-qMax(1,P(0))); scr->cx=0; break;
        case 'G': scr->cx=qMax(0,qMin(scr->cols-1,P(0)-1)); break;
        case 'H': case 'f':
            scr->cy=qMax(0,qMin(scr->rows-1,P(0,1)-1));
            scr->cx=qMax(0,qMin(scr->cols-1,P(1,1)-1));
            break;
        case 'J':{
            int m=P(0);
            if(m==0){for(int y=scr->cy+1;y<scr->rows;y++)scr->eraseLine(y);scr->clearLine(scr->cy,scr->cx,scr->cols-1);}
            else if(m==1){for(int y=0;y<scr->cy;y++)scr->eraseLine(y);scr->clearLine(scr->cy,0,scr->cx);}
            else if(m==2){for(int y=0;y<scr->rows;y++)scr->eraseLine(y);}
            else if(m==3){scr->scrollback.clear();}  // erase scrollback
            break;}
        case 'K':{
            int m=P(0);
            if(m==0) scr->clearLine(scr->cy,scr->cx,scr->cols-1);
            else if(m==1) scr->clearLine(scr->cy,0,scr->cx);
            else if(m==2) scr->eraseLine(scr->cy);
            break;}
        case 'L':{ int n=qMax(1,P(0)); for(int i=0;i<n;i++) scr->scrollDown(scr->cy,scrollBot); break;}
        case 'M':{ int n=qMax(1,P(0)); for(int i=0;i<n;i++) scr->scrollUp(scr->cy,scrollBot); break;}
        case 'P':{ // delete chars
            int n=qMax(1,P(0));
            auto &l=scr->lines[scr->cy];
            l.remove(scr->cx,n);
            while(l.size()<scr->cols) l.append(Cell{});
            break;}
        case '@':{ // insert chars
            int n=qMax(1,P(0));
            for(int i=0;i<n;i++) scr->lines[scr->cy].insert(scr->cx,Cell{});
            while(scr->lines[scr->cy].size()>scr->cols) scr->lines[scr->cy].removeLast();
            break;}
        case 'S': for(int i=0;i<qMax(1,P(0));i++) scr->scrollUp(scrollTop,scrollBot); break;
        case 'T': for(int i=0;i<qMax(1,P(0));i++) scr->scrollDown(scrollTop,scrollBot); break;
        case 'r':
            scrollTop=qMax(0,P(0,1)-1);
            scrollBot=qMin(scr->rows-1,P(1,scr->rows)-1);
            break;
        case 'd': scr->cy=qMax(0,qMin(scr->rows-1,P(0,1)-1)); break;
        case 'm': sgr(p); break;
        case 's': scr->sx=scr->cx; scr->sy=scr->cy; scr->sattr=scr->curAttr; break;
        case 'u': scr->cx=scr->sx; scr->cy=scr->sy; scr->curAttr=scr->sattr; break;
        case 'h': case 'l':
            if(seq.startsWith('?')){
                int n=seq.mid(1).toInt();
                if(n==25) scr->cursorVisible=(cmd=='h');
                else if(n==1049||n==1047||n==47){
                    if(cmd=='h') scr->switchToAlt();
                    else          scr->switchToNormal();
                }
                // ?2004: bracketed paste — acknowledge but ignore
                // ?7: auto-wrap — ignore for now
            }
            break;
        case 'c': // Primary DA — respond as VT220
            if(master>=0) { const char *da="\x1b[?62;1;22c"; write(master,da,strlen(da)); }
            break;
        case 'n': // DSR
            if(P(0)==5&&master>=0) { const char *ok="\x1b[0n"; write(master,ok,strlen(ok)); }
            else if(P(0)==6&&master>=0) { QByteArray r; r="\x1b["+QByteArray::number(scr->cy+1)+";"+QByteArray::number(scr->cx+1)+"R"; write(master,r.constData(),r.size()); }
            break;
        default: break;
        }
        scr->wrapNext=false;
    }

    void esc(char c){
        switch(c){
        case '7': scr->sx=scr->cx;scr->sy=scr->cy;scr->sattr=scr->curAttr; break;
        case '8': scr->cx=scr->sx;scr->cy=scr->sy;scr->curAttr=scr->sattr; break;
        case 'M': // reverse index
            if(scr->cy==scrollTop) scr->scrollDown(scrollTop,scrollBot);
            else scr->cy=qMax(0,scr->cy-1);
            break;
        case 'c': // full reset
            for(auto &l:scr->lines) for(auto &c2:l) c2={};
            scr->cx=scr->cy=0; scr->curAttr=Attr{};
            scrollTop=0; scrollBot=scr->rows-1;
            break;
        default: break;
        }
    }

    void sgr(const QList<int>&p){
        Attr &a=scr->curAttr;
        for(int i=0;i<p.size();i++){
            int n=p[i];
            if(n==0){a=Attr{};}
            else if(n==1) a.bold=true;
            else if(n==3) a.italic=true;
            else if(n==4) a.underline=true;
            else if(n==7) a.reverse=true;
            else if(n==21||n==22) a.bold=false;
            else if(n==23) a.italic=false;
            else if(n==24) a.underline=false;
            else if(n==27) a.reverse=false;
            else if(n>=30&&n<=37) a.fg=ansi16[n-30];
            else if(n==38){
                if(i+2<p.size()&&p[i+1]==5){a.fg=ansiColor(p[i+2]);i+=2;}
                else if(i+4<p.size()&&p[i+1]==2){a.fg=QColor(p[i+2],p[i+3],p[i+4]);i+=4;}
            }
            else if(n==39) a.fg=QColor(204,204,204);
            else if(n>=40&&n<=47) a.bg=ansi16[n-40];
            else if(n==48){
                if(i+2<p.size()&&p[i+1]==5){a.bg=ansiColor(p[i+2]);i+=2;}
                else if(i+4<p.size()&&p[i+1]==2){a.bg=QColor(p[i+2],p[i+3],p[i+4]);i+=4;}
            }
            else if(n==49) a.bg=QColor(0,0,0);
            else if(n>=90&&n<=97) a.fg=ansi16[n-90+8];
            else if(n>=100&&n<=107) a.bg=ansi16[n-100+8];
        }
    }
};


// ── Theme ─────────────────────────────────────────────────────────────────────
// Plain colour/gradient data. Previously loaded straight out of lumetask's
// shared ~/.lumetask/theme.json (parsing its "color1 color2 NNdeg"
// bg-primary convention) — now just a data holder, filled from and written
// to loomterminal's own config file (see TermWidget::loadConfig/saveConfig)
// so this terminal's colors are independent of whatever lumetask's theme
// says, while still supporting the same gradient+angle model.
struct Theme {
    QColor   highlight{255,144,83};
    QColor   bg1{0,0,0}, bg2{26,26,46};
    bool     gradient=false;
    double   angle=45.0;

    void loadFromJson(const QJsonObject &obj){
        if(obj.contains("highlight")) highlight=QColor(obj["highlight"].toString());
        if(obj.contains("bg1"))       bg1=QColor(obj["bg1"].toString());
        if(obj.contains("bg2"))       bg2=QColor(obj["bg2"].toString());
        if(obj.contains("gradient"))  gradient=obj["gradient"].toBool();
        if(obj.contains("angle"))     angle=obj["angle"].toDouble();
    }

    QJsonObject toJson() const {
        QJsonObject o;
        o["highlight"]=highlight.name();
        o["bg1"]=bg1.name();
        o["bg2"]=bg2.name();
        o["gradient"]=gradient;
        o["angle"]=angle;
        return o;
    }
};

// ── TermWidget ────────────────────────────────────────────────────────────────
class TermWidget : public QWidget {
    Q_OBJECT
private:
    Screen   *scr;
    VTParser *parser;
    QSocketNotifier *notifier;
    int master=-1;
    pid_t child=-1;

    QFont font;
    int cw, ch, baseline;

    // cursor blink
    QTimer *blinkTimer;
    bool blinkOn=true;

    // mouse selection
    bool selecting=false;
    QPoint selAnchor;

    // ── Scroll position ──────────────────────────────────────────────────
    // "Free scroll": the anchor is a FIXED, absolute line index (using
    // Screen::totalScrolledLines, which only ever counts up) marking which
    // line should sit at the top of the viewport. -1 means "not scrolled,
    // follow the live tail." Because it's an absolute point rather than a
    // count of "lines behind the live tail," it never needs to be
    // incrementally adjusted as new output arrives — it just stays where
    // you put it. scrollOffset is DERIVED from it (see refreshScrollOffset())
    // and is what the existing render/hit-test code below actually reads;
    // this replaces the old approach of incrementally "compensating"
    // scrollOffset on every onData() call, which came apart once the
    // scrollback cap made its size stop reflecting how much new output had
    // actually arrived (see the fix before this one).
    long long topAnchorAbs=-1;
    int scrollOffset=0;
    int padX=0, padY=0; // leftover pixels, distributed as padding

    // Scroll wheel sensitivity, in lines per tick. This is the one line to
    // change to adjust it — no other code needs to be touched.
    static constexpr double SCROLL_LINES_PER_TICK = 1.5;

    // Re-derives scrollOffset from topAnchorAbs. Call after anything changes
    // topAnchorAbs, or whenever new output may have arrived (topAnchorAbs
    // itself never needs to change for that — only its derived offset does,
    // since the "distance from bottom" naturally grows as the live tail
    // moves further from a fixed anchor point).
    void refreshScrollOffset(){
        if(topAnchorAbs<0){ scrollOffset=0; return; }
        long long sbSize=scr->scrollback.size();
        long long off=scr->totalScrolledLines-topAnchorAbs;
        off=qBound(0LL,off,sbSize);
        scrollOffset=(int)off;
        if(scrollOffset==0) topAnchorAbs=-1; // caught up to the live tail
    }

    // Sets scroll position to `v` lines back from the CURRENT live tail and
    // anchors it there absolutely — use this instead of assigning
    // scrollOffset directly so the anchor and derived offset never drift
    // apart from each other.
    void setScrollOffset(long long v){
        long long sbSize=scr->scrollback.size();
        v=qBound(0LL,v,sbSize);
        topAnchorAbs = (v>0) ? (scr->totalScrolledLines - v) : -1;
        scrollOffset=(int)v;
    }

    // settings
    Theme   theme;
    bool    enhancedColors=false;
    bool    boldAll=false;
    double  bgOpacity=1.0;  // Controls the theme/gradient opacity
    bool    cursorBar=false; // false = solid block cursor, true = blinking line/bar caret
    QWidget *settingsPanel=nullptr;
    bool    panelOpen=false;

    // ── Own config file ──────────────────────────────────────────────────
    // Everything the settings panel can change (colors/gradient, enhanced
    // colors, bold-all, background opacity, cursor style, font size) is
    // persisted here so it survives a restart — independent of lumetask's
    // ~/.lumetask/theme.json, which this terminal used to (mis)use as its
    // only source of color.
    static QString configPath(){
        QString dir = QDir::homePath()+"/.config/loomterminal";
        QDir().mkpath(dir);
        return dir+"/settings.json";
    }

    void loadConfig(){
        QFile f(configPath());
        if(!f.open(QIODevice::ReadOnly)) return;
        QJsonObject obj = QJsonDocument::fromJson(f.readAll()).object();
        theme.loadFromJson(obj);
        if(obj.contains("enhancedColors")) enhancedColors=obj["enhancedColors"].toBool();
        if(obj.contains("boldAll"))        boldAll=obj["boldAll"].toBool();
        if(obj.contains("bgOpacity"))      bgOpacity=obj["bgOpacity"].toDouble(1.0);
        if(obj.contains("cursorBar"))      cursorBar=obj["cursorBar"].toBool();
        if(obj.contains("fontSize"))       font.setPointSize(obj["fontSize"].toInt(11));
    }

    void saveConfig(){
        QJsonObject obj = theme.toJson();
        obj["enhancedColors"]=enhancedColors;
        obj["boldAll"]=boldAll;
        obj["bgOpacity"]=bgOpacity;
        obj["cursorBar"]=cursorBar;
        obj["fontSize"]=font.pointSize();
        QFile f(configPath());
        if(f.open(QIODevice::WriteOnly|QIODevice::Truncate)){
            f.write(QJsonDocument(obj).toJson(QJsonDocument::Indented));
        }
    }

public:
    TermWidget(QWidget *parent=nullptr):QWidget(parent){
        setAttribute(Qt::WA_OpaquePaintEvent);
        setFocusPolicy(Qt::StrongFocus);
        setCursor(Qt::IBeamCursor);
        setSizePolicy(QSizePolicy::Expanding, QSizePolicy::Expanding);

        font=QFont("Monospace",11);
        font.setStyleHint(QFont::TypeWriter);

        // Load persisted settings (colors/gradient, cursor style, font size,
        // etc.) before computing font metrics, so a saved font size takes
        // effect from the very first frame instead of one resize later.
        loadConfig();

        QFontMetrics fm(font);
        cw=fm.horizontalAdvance('M');
        ch=fm.lineSpacing();
        baseline=fm.ascent();

        // initial size — will be corrected on first resizeEvent
        scr=new Screen(80,24);
        parser=new VTParser(scr);

        struct winsize ws{};
        ws.ws_col=scr->cols; ws.ws_row=scr->rows;

        child=forkpty(&master,nullptr,nullptr,&ws);
        if(child==0){
            setenv("TERM","xterm-256color",1);
            setenv("SHELL","/bin/bash",1);
            setenv("COLORTERM","truecolor",1);
            execlp("bash","bash",nullptr);
            _exit(1);
        }
        fcntl(master,F_SETFL,O_NONBLOCK);
        parser->master=master;

        notifier=new QSocketNotifier(master,QSocketNotifier::Read,this);
        connect(notifier,&QSocketNotifier::activated,this,&TermWidget::onData);

        blinkTimer=new QTimer(this);
        connect(blinkTimer,&QTimer::timeout,[this]{
            blinkOn=!blinkOn; update();
        });
        blinkTimer->start(500);

        // build settings panel
        buildSettingsPanel();
    }

    ~TermWidget(){
        if(child>0) kill(child,SIGHUP);
    }

    QSize sizeHint() const override { return QSize(); }

private slots:
    void onData(){
        char buf[8192];
        ssize_t n=read(master,buf,sizeof(buf));
        if(n<=0) return;
        parser->feed(QByteArray(buf,n));
        // Free scroll: topAnchorAbs is a fixed point, so there's nothing to
        // "compensate" here at all — just re-derive scrollOffset from it.
        // No incremental math, so no way for it to drift regardless of how
        // fast output arrives or how the scrollback cap churns.
        refreshScrollOffset();
        update();
    }

protected:
    void paintEvent(QPaintEvent *) override {
        QPainter p(this);
        p.setFont(font);

        // Draw the theme background with opacity
        if(theme.gradient){
            double rad=theme.angle*M_PI/180.0;
            double cx2=width()/2.0, cy2=height()/2.0;
            double dx=cos(rad)*width()/2.0, dy=sin(rad)*height()/2.0;
            QLinearGradient grad(cx2-dx,cy2-dy,cx2+dx,cy2+dy);
            QColor bg1 = theme.bg1;
            QColor bg2 = theme.bg2;
            bg1.setAlphaF(bgOpacity);
            bg2.setAlphaF(bgOpacity);
            grad.setColorAt(0,bg1);
            grad.setColorAt(1,bg2);
            p.fillRect(rect(),grad);
        } else {
            QColor bg = theme.bg1;
            bg.setAlphaF(bgOpacity);
            p.fillRect(rect(),bg);
        }

        int sbSize=scr->scrollback.size();
        int totalRows=sbSize+scr->rows;
        int visRows=scr->rows;
        int firstRow=totalRows-scr->rows-scrollOffset;
        firstRow=qMax(0,firstRow);

        for(int row=0;row<visRows;row++){
            int srcRow=firstRow+row;
            const QVector<Cell>*line=nullptr;
            if(srcRow<sbSize) line=&scr->scrollback[srcRow];
            else if(srcRow-sbSize<scr->rows) line=&scr->lines[srcRow-sbSize];
            else break;

            int y=padY+row*ch;
            for(int col=0;col<scr->cols&&col<line->size();col++){
                const Cell &cell=(*line)[col];
                Attr a=cell.attr;

                QColor fg=a.bold&&a.fg==QColor(204,204,204)?Qt::white:a.fg;
                QColor bg=a.bg;

                if(a.reverse) qSwap(fg,bg);

                // If the resulting BACKGROUND is black (0,0,0), make it
                // transparent so the compositor's theme shows through. This
                // must run AFTER the reverse-video swap above, not before —
                // otherwise a reverse cell (nano's title/status bars: default
                // colors + SGR7, no explicit color pair) has its original
                // black bg zeroed to alpha=0 and then swapped INTO the fg
                // slot, so the text gets drawn in a fully transparent color:
                // invisible ink on a solid box, instead of dark text on a
                // light background.
                if(bg == QColor(0,0,0)) {
                    bg.setAlpha(0);
                }

                bool inSel=false;
                if(scr->selStartY>=0){
                    int ay=scr->selStartY,ax=scr->selStartX;
                    int by=scr->selEndY,  bx=scr->selEndX;
                    if(ay>by||(ay==by&&ax>bx)){qSwap(ay,by);qSwap(ax,bx);}
                    int vy=srcRow,vx=col;
                    if(vy>ay||(vy==ay&&vx>=ax))
                        if(vy<by||(vy==by&&vx<=bx)) inSel=true;
                }
                if(inSel){ fg=Qt::black; bg=theme.highlight; }

                // enhanced colors: boost saturation
                if(enhancedColors&&!inSel){
                    auto boost=[](QColor c)->QColor{
                        int h,s,v,a; c.getHsv(&h,&s,&v,&a);
                        s=qMin(255,int(s*1.5)); v=qMin(255,int(v*1.1));
                        c.setHsv(h,s,v,a); return c;
                    };
                    fg=boost(fg);
                }
                // bold all
                if(boldAll) a.bold=true;

                int x=padX+col*cw;
                
                // Only draw background if it's not transparent
                if(bg.alpha() > 0) {
                    p.fillRect(x,y,cw,ch,bg);
                }
                
                if(!cell.ch.isSpace()){
                    p.setPen(fg);
                    if(a.bold){ QFont bf=font; bf.setBold(true); p.setFont(bf); }
                    if(a.italic){ QFont itf=p.font(); itf.setItalic(true); p.setFont(itf); }
                    p.drawText(x,y+baseline,cell.ch);
                    if(a.bold||a.italic) p.setFont(font);
                    if(a.underline) p.drawLine(x,y+baseline+1,x+cw,y+baseline+1);
                }
            }
        }

        // cursor
        if(scr->cursorVisible&&scrollOffset==0&&blinkOn){
            int cx=scr->cx, cy=scr->cy;
            int x=padX+cx*cw, y=padY+cy*ch;
            if(cursorBar){
                // Blinking bar/line caret at the cell's left edge, like a
                // text-insertion point — the glyph underneath is already
                // drawn in its normal color by the loop above, so there's
                // nothing else to redraw here.
                p.fillRect(x,y,qMax(2,cw/6),ch,QColor(220,220,220));
            } else {
                p.fillRect(x,y,cw,ch,QColor(220,220,220));
                const Cell &cc=scr->lines[cy][qMin(cx,scr->cols-1)];
                if(!cc.ch.isSpace()){
                    p.setPen(Qt::black);
                    p.drawText(x,y+baseline,cc.ch);
                }
            }
        }
    }

    void resizeEvent(QResizeEvent *ev) override {
        QWidget::resizeEvent(ev);
        if(settingsPanel&&panelOpen){
            int pw=qMin(260,width());
            settingsPanel->setGeometry(width()-pw,0,pw,height());
        }
        int cols=qMax(1,width()/cw);
        int rows=qMax(1,height()/ch);
        padX=(width()  - cols*cw)/2;
        padY=(height() - rows*ch)/2;
        scr->resize(cols,rows);
        parser->scrollBot=rows-1;
        struct winsize ws{};
        ws.ws_col=cols; ws.ws_row=rows;
        ioctl(master,TIOCSWINSZ,&ws);
    }

    void updateFont(int ptSize){
        if(ptSize < 6 || ptSize > 72) return;
        font.setPointSize(ptSize);
        QFontMetrics fm(font);
        cw       = fm.horizontalAdvance('M');
        ch       = fm.lineSpacing();
        baseline = fm.ascent();
        int cols = qMax(1, width()  / cw);
        int rows = qMax(1, height() / ch);
        padX = (width()  - cols*cw) / 2;
        padY = (height() - rows*ch) / 2;
        scr->resize(cols, rows);
        parser->scrollBot = rows - 1;
        struct winsize ws{};
        ws.ws_col = cols;
        ws.ws_row = rows;
        ioctl(master, TIOCSWINSZ, &ws);
        update();
        saveConfig();
    }

public:
    void buildSettingsPanel(){
        settingsPanel = new QWidget(this, Qt::Popup);
        settingsPanel->setObjectName("settingsPanel");
        settingsPanel->setStyleSheet(
            "#settingsPanel{"
            "  background:rgba(20,20,20,230);"
            "  border-left:1px solid #333;"
            "  border-radius:8px;"
            "}"
            "QLabel{ color:#ccc; font-size:13px; }"
            "QCheckBox{ color:#ccc; font-size:13px; }"
            "QCheckBox::indicator{ width:16px;height:16px; }"
            "QSlider::groove:horizontal{ background:#333;height:4px;border-radius:2px; }"
            "QSlider::handle:horizontal{ background:#ff9053;width:14px;height:14px;margin:-5px 0;border-radius:7px; }"
            "QSlider::sub-page:horizontal{ background:#ff9053;border-radius:2px; }"
            "QPushButton{ background:#2a2a2a;color:#ccc;border:1px solid #444;"
            "  border-radius:4px;padding:5px 8px;font-size:12px; }"
            "QPushButton:hover{ background:#333; }"
        );

        auto *vl = new QVBoxLayout(settingsPanel);
        vl->setContentsMargins(16,20,16,20);
        vl->setSpacing(18);

        auto *title = new QLabel("Settings", settingsPanel);
        title->setStyleSheet("color:#ff9053;font-size:15px;font-weight:bold;");
        vl->addWidget(title);

        // enhanced colors
        auto *cbEnhanced = new QCheckBox("Enhanced Colors", settingsPanel);
        cbEnhanced->setChecked(enhancedColors);
        connect(cbEnhanced, &QCheckBox::toggled, [this](bool v){ enhancedColors=v; update(); saveConfig(); });
        vl->addWidget(cbEnhanced);

        // bold text
        auto *cbBold = new QCheckBox("Bold Text", settingsPanel);
        cbBold->setChecked(boldAll);
        connect(cbBold, &QCheckBox::toggled, [this](bool v){ boldAll=v; update(); saveConfig(); });
        vl->addWidget(cbBold);

        // cursor style — solid block (default) vs a blinking line/bar caret
        auto *cbCursorBar = new QCheckBox("Line Cursor", settingsPanel);
        cbCursorBar->setChecked(cursorBar);
        connect(cbCursorBar, &QCheckBox::toggled, [this](bool v){ cursorBar=v; update(); saveConfig(); });
        vl->addWidget(cbCursorBar);

        // Background opacity - controls the theme/gradient opacity
        auto *lblOp = new QLabel("Background Opacity", settingsPanel);
        vl->addWidget(lblOp);
        auto *slOp = new QSlider(Qt::Horizontal, settingsPanel);
        slOp->setRange(0,100);
        slOp->setValue(int(bgOpacity*100));
        connect(slOp, &QSlider::valueChanged, [this](int v){
            bgOpacity = v/100.0;
            update();
            saveConfig();
        });
        vl->addWidget(slOp);

        // gradient toggle + the two colors + angle it blends across.
        // Independent of lumetask's theme now — these are loomterminal's
        // own settings, persisted to loomterminal's own config file.
        auto *cbGradient = new QCheckBox("Gradient Background", settingsPanel);
        cbGradient->setChecked(theme.gradient);
        vl->addWidget(cbGradient);

        auto *btnBg1 = new QPushButton("Background Color 1", settingsPanel);
        vl->addWidget(btnBg1);
        auto *btnBg2 = new QPushButton("Background Color 2", settingsPanel);
        btnBg2->setEnabled(theme.gradient);
        vl->addWidget(btnBg2);

        auto *lblAngle = new QLabel("Gradient Angle", settingsPanel);
        lblAngle->setEnabled(theme.gradient);
        vl->addWidget(lblAngle);
        auto *slAngle = new QSlider(Qt::Horizontal, settingsPanel);
        slAngle->setRange(0,360);
        slAngle->setValue(int(theme.angle));
        slAngle->setEnabled(theme.gradient);
        vl->addWidget(slAngle);

        connect(cbGradient, &QCheckBox::toggled, [this,btnBg2,lblAngle,slAngle](bool v){
            theme.gradient=v;
            btnBg2->setEnabled(v);
            lblAngle->setEnabled(v);
            slAngle->setEnabled(v);
            update();
            saveConfig();
        });
        connect(btnBg1, &QPushButton::clicked, [this]{
            QColor c = QColorDialog::getColor(theme.bg1, this, "Background Color 1");
            if(c.isValid()){ theme.bg1=c; update(); saveConfig(); }
        });
        connect(btnBg2, &QPushButton::clicked, [this]{
            QColor c = QColorDialog::getColor(theme.bg2, this, "Background Color 2");
            if(c.isValid()){ theme.bg2=c; update(); saveConfig(); }
        });
        connect(slAngle, &QSlider::valueChanged, [this](int v){
            theme.angle=v;
            update();
            saveConfig();
        });

        vl->addStretch();

        auto *hint = new QLabel("F1 to close", settingsPanel);
        hint->setStyleSheet("color:#555;font-size:11px;");
        vl->addWidget(hint);

        settingsPanel->hide();
    }

    void toggleSettings(){
        if(!settingsPanel) return;
        if(!panelOpen){
            int panelW = qMin(260, width());
            int panelH = height();
            QPoint globalPos = mapToGlobal(QPoint(width() - panelW, 0));
            settingsPanel->setGeometry(globalPos.x(), globalPos.y(), panelW, panelH);
            settingsPanel->show();
            settingsPanel->raise();
            panelOpen = true;
        } else {
            settingsPanel->hide();
            panelOpen = false;
        }
    }

    void keyPressEvent(QKeyEvent *ke) override {
        QByteArray data;
        bool ctrl=ke->modifiers()&Qt::ControlModifier;
        bool shift=ke->modifiers()&Qt::ShiftModifier;

        if(ctrl&&shift){
            if(ke->key()==Qt::Key_C){
                QString sel=scr->selectedText();
                if(!sel.isEmpty()) QApplication::clipboard()->setText(sel);
                return;
            }
            if(ke->key()==Qt::Key_V){
                QString clip=QApplication::clipboard()->text();
                write(master,clip.toUtf8().constData(),clip.toUtf8().size());
                return;
            }
        }

        if(ke->key()==Qt::Key_F1){ toggleSettings(); return; }

        if(ctrl&&(ke->key()==Qt::Key_Equal||ke->key()==Qt::Key_Plus)){
            updateFont(font.pointSize()+1); return;
        }
        if(ctrl&&ke->key()==Qt::Key_Minus){
            updateFont(font.pointSize()-1); return;
        }
        if(ctrl&&ke->key()==Qt::Key_0){
            updateFont(11); return;
        }

        if(ctrl && !shift){
            int k=ke->key();
            if(k>=Qt::Key_A&&k<=Qt::Key_Z){
                data=QByteArray(1,char(k-Qt::Key_A+1));
            } else if(k==Qt::Key_BracketLeft)  data="\x1b";
            else if(k==Qt::Key_Backslash)       data="\x1c";
            else if(k==Qt::Key_BracketRight)    data="\x1d";
            else if(k==Qt::Key_Space)           data=QByteArray(1,char(0));
            else if(k==Qt::Key_Underscore)      data=QByteArray(1,char(31));
            if(!data.isEmpty()){ setScrollOffset(0); write(master,data.constData(),data.size()); return; }
        }

        switch(ke->key()){
        case Qt::Key_Return:
        case Qt::Key_Enter:     data="\r"; break;
        case Qt::Key_Backspace: data="\x7f"; break;
        case Qt::Key_Tab:       data=shift?"\x1b[Z":"\t"; break;
        case Qt::Key_Up:        data="\x1b[A"; break;
        case Qt::Key_Down:      data="\x1b[B"; break;
        case Qt::Key_Right:     data="\x1b[C"; break;
        case Qt::Key_Left:      data="\x1b[D"; break;
        case Qt::Key_Home:      data="\x1b[H"; break;
        case Qt::Key_End:       data="\x1b[F"; break;
        case Qt::Key_PageUp:
            // Full-screen apps (vim, nano, less, man, ...) live in the
            // alternate screen and own their own paging — forward the real
            // key instead of scrolling our local (and, for them,
            // irrelevant) scrollback view. Only the normal screen (shell
            // prompt) uses PageUp/PageDown to browse local history.
            if(scr->altActive){ data="\x1b[5~"; break; }
            setScrollOffset(scrollOffset+scr->rows/2);
            update(); return;
        case Qt::Key_PageDown:
            if(scr->altActive){ data="\x1b[6~"; break; }
            setScrollOffset(scrollOffset-scr->rows/2);
            update(); return;
        case Qt::Key_Delete:    data="\x1b[3~"; break;
        case Qt::Key_Insert:    data="\x1b[2~"; break;
        case Qt::Key_F1:        data="\x1bOP"; break;
        case Qt::Key_F2:        data="\x1bOQ"; break;
        case Qt::Key_F3:        data="\x1bOR"; break;
        case Qt::Key_F4:        data="\x1bOS"; break;
        case Qt::Key_F5:        data="\x1b[15~"; break;
        case Qt::Key_F6:        data="\x1b[17~"; break;
        case Qt::Key_F7:        data="\x1b[18~"; break;
        case Qt::Key_F8:        data="\x1b[19~"; break;
        case Qt::Key_F9:        data="\x1b[20~"; break;
        case Qt::Key_F10:       data="\x1b[21~"; break;
        case Qt::Key_F11:       data="\x1b[23~"; break;
        case Qt::Key_F12:       data="\x1b[24~"; break;
        default:
            data=ke->text().toUtf8();
        }
        if(!data.isEmpty()){
            setScrollOffset(0);
            write(master,data.constData(),data.size());
        }
    }

    void mousePressEvent(QMouseEvent *ev) override {
        setFocus();
        if(ev->button()==Qt::LeftButton){
            bool shift=ev->modifiers()&Qt::ShiftModifier;
            if(shift && scr->selStartY>=0){
                int sbSize=scr->scrollback.size();
                scr->selEndX=qMax(0,qMin(scr->cols-1,(ev->x()-padX)/cw));
                scr->selEndY=sbSize-scrollOffset+(ev->y()-padY)/ch;
                selecting=true;
                selAnchor=QPoint(scr->selStartX*cw,
                    (scr->selStartY-(sbSize-scrollOffset))*ch);
            } else {
                scr->selStartY=scr->selEndY=-1;
                selAnchor=ev->pos();
                selecting=false;
            }
            update();
        }
    }

    void mouseMoveEvent(QMouseEvent *ev) override {
        if(!(ev->buttons()&Qt::LeftButton)) return;
        if(!selecting){
            if((ev->pos()-selAnchor).manhattanLength()<4) return;
            selecting=true;
            scr->selStartX=(selAnchor.x()-padX)/cw;
            int sbSize0=scr->scrollback.size();
            scr->selStartY=sbSize0-scrollOffset+(selAnchor.y()-padY)/ch;
        }
        scr->selEndX=qMax(0,qMin(scr->cols-1,(ev->x()-padX)/cw));
        int sbSize=scr->scrollback.size();
        scr->selEndY=sbSize-scrollOffset+(ev->y()-padY)/ch;
        update();
    }

    void mouseReleaseEvent(QMouseEvent *ev) override {
        if(ev->button()==Qt::LeftButton) selecting=false;
        if(ev->button()==Qt::MiddleButton){
            QString clip=QApplication::clipboard()->text(QClipboard::Selection);
            if(clip.isEmpty()) clip=QApplication::clipboard()->text();
            write(master,clip.toUtf8().constData(),clip.toUtf8().size());
        }
        QString sel=scr->selectedText();
        if(!sel.isEmpty())
            QApplication::clipboard()->setText(sel,QClipboard::Selection);
    }

    void mouseDoubleClickEvent(QMouseEvent *ev) override {
        int col=ev->x()/cw;
        int sbSize=scr->scrollback.size();
        int row=sbSize-scrollOffset+ev->y()/ch;
        if(row<0||row>=sbSize+scr->rows) return;
        const QVector<Cell>*line=nullptr;
        if(row<sbSize) line=&scr->scrollback[row];
        else if(row-sbSize<scr->rows) line=&scr->lines[row-sbSize];
        if(!line) return;
        int x0=col,x1=col;
        auto isWord=[&](int x)->bool{
            if(x<0||x>=line->size()) return false;
            QChar c=(*line)[x].ch;
            return c.isLetterOrNumber()||c=='_'||c=='-'||c=='.'||c=='/';
        };
        while(isWord(x0-1)) x0--;
        while(isWord(x1+1)) x1++;
        scr->selStartX=x0; scr->selEndX=x1;
        scr->selStartY=scr->selEndY=row;
        QString sel=scr->selectedText();
        if(!sel.isEmpty()) QApplication::clipboard()->setText(sel,QClipboard::Selection);
        update();
    }

    void wheelEvent(QWheelEvent *ev) override {
        int dy=ev->angleDelta().y();
        // A two-finger touchpad swipe's kinetic/momentum sequence ends with
        // a "stop" tick carrying a genuinely zero delta (Qt's signal that
        // the gesture is settling, not a real scroll step). The old
        // `dy>0?+3:-3` ternary treated that zero as "not > 0" and scrolled
        // DOWN by 3 regardless — invisible mid-scroll, but glaringly
        // obvious exactly at the top, where you'd just hit the hard
        // boundary and then get visibly kicked back down as the gesture
        // finished. Only after enough scrollback exists to actually reach
        // and notice that boundary, which matches what was reported.
        if(dy==0) return;
        int whole=qRound(dy>0 ? SCROLL_LINES_PER_TICK : -SCROLL_LINES_PER_TICK);
        if(whole==0){ update(); return; }

        if(scr->altActive){
            // Full-screen apps (vim, nano, less, man, ...) live in the
            // alternate screen and have their own content — our local
            // scrollback view doesn't mean anything to them. We haven't
            // implemented full SGR/X10 mouse-wheel reporting, so forward
            // the wheel as repeated arrow-key presses instead: the same
            // xterm-compatible fallback real terminals use, and every app
            // in that list already handles Up/Down for scrolling.
            const char *seq = whole>0 ? "\x1b[A" : "\x1b[B";
            for(int i=0;i<qAbs(whole);i++) write(master,seq,3);
            return;
        }
        setScrollOffset(scrollOffset+whole);
        update();
    }

    void contextMenuEvent(QContextMenuEvent *ev) override {
        QMenu menu(this);
        menu.addAction("Copy  Ctrl+Shift+C",[this]{
            QString sel=scr->selectedText();
            if(!sel.isEmpty()) QApplication::clipboard()->setText(sel);
        });
        menu.addAction("Paste  Ctrl+Shift+V",[this]{
            QString clip=QApplication::clipboard()->text();
            write(master,clip.toUtf8().constData(),clip.toUtf8().size());
        });
        menu.addSeparator();
        menu.addAction("Font +  Ctrl+Shift+=",[this]{ updateFont(font.pointSize()+1); });
        menu.addAction("Font -  Ctrl+Shift+-",[this]{ updateFont(font.pointSize()-1); });
        menu.exec(ev->globalPos());
    }
};

#include "terminal.moc"

int main(int argc,char *argv[]){
    QApplication app(argc,argv);
    app.setApplicationName("Terminal");

    QWidget win;
    win.setWindowTitle("Terminal");
    win.setStyleSheet("background:#000;");
    auto *layout=new QVBoxLayout(&win);
    layout->setContentsMargins(0,0,0,0);
    auto *term=new TermWidget(&win);
    layout->addWidget(term);
    win.show();
    return app.exec();
}
