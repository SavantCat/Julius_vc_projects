/* 
 *  libjcode.c -- ´Á»úÊÑ´¹¥é¥¤¥Ö¥é¥E   1.0 ÈÇ
 *                (C) Kuramitsu Kimio, Tokyo Univ. 1996-97
 *
 *  ¤³¤Î¥é¥¤¥Ö¥é¥ê¤Ï¡¢CGI Programming with C and Perl ¤Î¤¿¤á¤Ë
 *  Ken Lunde ÃE¡ÖÆEÜ¸EğÊó½èÍı¡× (O'llery) ¤ò»²¹Í¤Ë¤·¤Æ¡¢
 *  ¥¹¥È¥ê¡¼¥àÍÑ¤À¤Ã¤¿jconv.c ¤ò¡¢¥¹¥È¥Eó¥°ÂĞ±ş¤Ë¤·¤Æ¥é¥¤¥Ö¥é¥E½
 *  ¤·¤Ş¤·¤¿¡£ 
 *  ¤¿¤À¤·¡¢CGI (INTERNET)¤Ç¤ÎÍøÍÑ¤ò¹Í¤¨¤Æ¡¢ÊÑ¹¹¤·¤Æ¤¢¤ê¤Ş¤¹¡£
 */

/* modified by ri to avoid may malloc */
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <locale.h>
#include "jlib.h"
#include "jlibconfig.h"

#include <sent/stddefs.h>
 
extern int detectKanjiCode(char *str);
static unsigned char *_to_jis(unsigned char *str);
static unsigned char *_to_ascii(unsigned char *str);
static void _jis_shift(int *p1, int *p2);
static void _sjis_shift(int *p1, int *p2);
static unsigned char *_sjis_han2zen(unsigned char *str, int *p1, int *p2);
static void _shift2seven(unsigned char *str, unsigned char *str2);
static void _shift2euc(unsigned char *str, unsigned char *str2);
static void _shift_self(unsigned char *str, unsigned char *str2);
static void _euc2seven(unsigned char *str, unsigned char *str2);
static void _euc2shift(unsigned char *str, unsigned char *str2);
static unsigned char *_skip_esc(unsigned char *str, int *esc_in);
static void _seven2shift(unsigned char *str, unsigned char *str2);
static void _seven2euc(unsigned char *str, unsigned char *str2);



#define CHAROUT(ch) *str2 = (unsigned char)(ch); str2++;

/* --------------------------------------- JIS(ISO-2022) ¥³¡¼¥É¤ØÀÚ¤EØ¤¨ -- */

static unsigned char *_to_jis(unsigned char *str) {
  *str = (unsigned char)ESC; str++;
  *str = (unsigned char)'$'; str++;
  *str = (unsigned char)'B'; str++;
  return str;
}

/* ----------------------------------------------- ASCII ¥³¡¼¥É¤ØÀÚ¤EØ¤¨ -- */

/* ESC ( B ¤È ESC ( J ¤Î°ã¤¤¡£
   ËÜÍè¤Ï¡¢ ESC ( J ¤¬Àµ¤·¤¤JIS-Roman ÂÎ·Ï¤Ç¤¢¤E¬¡¢
   ¥¤¥ó¥¿¡¼¥Í¥Ã¥È¤Î¾å¤Ç¤Ï¡¢±Ñ¿ô»ú¤ÏASCII ¤ÎÊı¤¬¼«Á³¤«¤È»×¤EEE£
   \ µ­¹æ¤È ~µ­¹æ¤¬°ã¤¦¤À¤±¤Ç¤¢¤E£ */

static unsigned char *_to_ascii(unsigned char *str) {
  *str = (unsigned char)ESC; str++;
  *str = (unsigned char)'('; str++;
  *str = (unsigned char)'B'; str++;
  return str;
}

/* -------------------------------------- JIS ¥³¡¼¥É ¤ESJIS¤È¤·¤Æ¥·¥Õ¥È -- */

static void _jis_shift(int *p1, int *p2)
{
  unsigned char c1 = *p1;
  unsigned char c2 = *p2;
  int rowOffset = c1 < 95 ? 112 : 176;
  int cellOffset = c1 % 2 ? (c2 > 95 ? 32 : 31) : 126;

  *p1 = ((c1 + 1) >> 1) + rowOffset;
  *p2 += cellOffset;
}

/* --------------------------------- SJIS ¥³¡¼¥É¤òJIS ¥³¡¼¥É¤È¤·¤Æ¥·¥Õ¥È -- */

static void _sjis_shift(int *p1, int *p2)
{
  unsigned char c1 = *p1;
  unsigned char c2 = *p2;
  int adjust = c2 < 159;
  int rowOffset = c1 < 160 ? 112 : 176;
  int cellOffset = adjust ? (c2 > 127 ? 32 : 31) : 126;

  *p1 = ((c1 - rowOffset) << 1) - adjust;
  *p2 -= cellOffset;
}

/* ---------------------------------------------- SJIS È¾³Ñ¤òÁ´³Ñ¤ËÊÑ´¹ -- */
#define HANKATA(a)  (a >= 161 && a <= 223)
#define ISMARU(a)   (a >= 202 && a <= 206)
#define ISNIGORI(a) ((a >= 182 && a <= 196) || (a >= 202 && a <= 206) || (a == 179))

static int stable[][2] = {
    {129,66},{129,117},{129,118},{129,65},{129,69},{131,146},{131,64},
    {131,66},{131,68},{131,70},{131,72},{131,131},{131,133},{131,135},
    {131,98},{129,91},{131,65},{131,67},{131,69},{131,71},{131,73},
    {131,74},{131,76},{131,78},{131,80},{131,82},{131,84},{131,86},
    {131,88},{131,90},{131,92},{131,94},{131,96},{131,99},{131,101},
    {131,103},{131,105},{131,106},{131,107},{131,108},{131,109},
    {131,110},{131,113},{131,116},{131,119},{131,122},{131,125},
    {131,126},{131,128},{131,129},{131,130},{131,132},{131,134},
    {131,136},{131,137},{131,138},{131,139},{131,140},{131,141},
    {131,143},{131,147},{129,74},{129,75}};

static unsigned char *_sjis_han2zen(unsigned char *str, int *p1, int *p2)
{
  register int c1, c2;

  c1 = (int)*str; str++;
  *p1 = stable[c1 - 161][0];
  *p2 = stable[c1 - 161][1];

  /* Âù²»¡¢È¾Âù²»¤Î½èÍı */
  c2 = (int)*str;
  if (c2 == 222 && ISNIGORI(c1)) {
    if ((*p2 >= 74 && *p2 <= 103) || (*p2 >= 110 && *p2 <= 122))
      (*p2)++;
    else if (*p1 == 131 && *p2 == 69)
      *p2 = 148;
    str++;
  }

  if (c2 == 223 && ISMARU(c1) && (*p2 >= 110 && *p2 <= 122) ) {
    *p2 += 2;
    str++;
  }
  return str++;
}

/* -------------------------------------------------- SJIS ¥³¡¼¥É¤òÊÑ´¹ -- */

#define SJIS1(A)    ((A >= 129 && A <= 159) || (A >= 224 && A <= 239))
#define SJIS2(A)    (A >= 64 && A <= 252)

static void _shift2seven(unsigned char *str, unsigned char *str2)
{
  int p1,p2,esc_in = FALSE;

  while ((p1 = (int)*str) != '\0') {

    if (SJIS1(p1)) {
      if((p2 = (int)*(++str)) == '\0') break;
      if (SJIS2(p2)) {
        _sjis_shift(&p1,&p2);
        if (!esc_in) {
          esc_in = TRUE;
          str2 = _to_jis(str2);
        }
      }
      CHAROUT(p1);
      CHAROUT(p2);
      str++;
      continue;
    }

#ifdef NO_HANKAKU_SJIS
    /* È¾³Ñ SJIS ¤Ï¡¢¶¯À©Åª¤ËÁ´³Ñ¤ËÊÑ¤¨¤E*/
    if (HANKATA(p1)) {
      str = _sjis_han2zen(str, &p1, &p2);
      _sjis_shift(&p1,&p2);
      if (!esc_in) {
        esc_in = TRUE;
        str2 = _to_jis(str2);
      }
      CHAROUT(p1);
      CHAROUT(p2);
      continue;
    }
#endif

    if (esc_in) {
      /* LF / CR ¤Î¾Eç¤Ï¡¢Àµ¾EË¥¨¥¹¥±¡¼¥×¥¢¥¦¥È¤µ¤EE*/
      esc_in = FALSE;
      str2 = _to_ascii(str2);
    }
    CHAROUT(p1);
    str++;
  }

  if (esc_in)
    str2 = _to_ascii(str2);
  *str2='\0';
}

/* --------------------------------------------- SJIS ¤EEUC ¤ËÊÑ´¹¤¹¤E-- */

static void _shift2euc(unsigned char *str, unsigned char *str2)
{
  int p1,p2;
  
  while ((p1 = (int)*str) != '\0') {
    if (SJIS1(p1)) {
      if((p2 = (int)*(++str)) == '\0') break;
      if (SJIS2(p2)) {
        _sjis_shift(&p1,&p2);
        p1 += 128;
        p2 += 128;
      }
      CHAROUT(p1);
      CHAROUT(p2);
      str++;
      continue;
    }

#ifdef NO_HANKAKU_SJIS
    /* È¾³Ñ SJIS ¤Ï¡¢¶¯À©Åª¤ËÁ´³Ñ¤ËÊÑ¤¨¤E*/
    if (HANKATA(p1)) {
      str = _sjis_han2zen(str,&p1,&p2);
      _sjis_shift(&p1,&p2);
      p1 += 128;
      p2 += 128;
      CHAROUT(p1);
      CHAROUT(p2);
      continue;
    }
#endif
    CHAROUT(p1);
    str++;
  }
  *str2='\0';
}

/* ------------------------------------------------- È¾³Ñ SJIS ¤ò¼è¤EE¯ -- */

static void _shift_self(unsigned char *str, unsigned char *str2)
{
  int p1;
  
  while ((p1 = (int)*str) != '\0') {
#ifdef NO_HANKAKU_SJIS
    /* È¾³Ñ SJIS ¤Ï¡¢¶¯À©Åª¤ËÁ´³Ñ¤ËÊÑ¤¨¤E*/
    if (HANKATA(p1)) {
      str = _sjis_han2zen(str, &p1, &p2);
      CHAROUT(p1);
      CHAROUT(p2);
      continue;
    }
#endif
    CHAROUT(p1);
    str++;
  }
  *str2='\0';
}

/* ------------------------------------------------------EUC ¤«¤EJIS ¤Ø -- */

#define ISEUC(A)    (A >= 161 && A <= 254)

static void _euc2seven(unsigned char *str, unsigned char *str2)
{
  int p1, p2, esc_in = FALSE;

  while ((p1 = (int)*str) != '\0') {

    if (p1 == LF || p1 == CR) {
      if (esc_in) {
        esc_in = FALSE;
        str2 = _to_ascii(str2);
      }
      CHAROUT(p1);
      str++;
      continue;
    }

    if (ISEUC(p1)) {
      if((p2 = (int)*(++str)) == '\0') break;
      if (ISEUC(p2)) {

	if (!esc_in) {
	  esc_in = TRUE;
	  str2 =_to_jis(str2);
	}

	CHAROUT(p1-128);
	CHAROUT(p2-128);
	str++;
	continue;
      }
    }

    if (esc_in) {
      esc_in = FALSE;
      str2 = _to_ascii(str2);
    }
    CHAROUT(p1);
    str++;
  }
  *str2='\0';
}

/* ------------------------------------------------ EUC ¤«¤ESJIS ¤ËÊÑ´¹ -- */
 
static void _euc2shift(unsigned char *str, unsigned char *str2)
{
  int p1,p2;

  while ((p1 = (int)*str) != '\0') {
    if (ISEUC(p1)) {
      if((p2 = (int)*(++str)) == '\0') break;
      if (ISEUC(p2)) {
	p1 -= 128;
        p2 -= 128;
        _jis_shift(&p1,&p2);
      }
      CHAROUT(p1);
      CHAROUT(p2);
      str++;
      continue;
    }

    CHAROUT(p1);
    str++;
  }
  *str2='\0';
}

/* -------------------------------------- ESC ¥·¡¼¥±¥ó¥¹¤ò¥¹¥­¥Ã¥×¤¹¤E----- */

static unsigned char *_skip_esc(unsigned char *str, int *esc_in) {
  int c;
  
  c = (int)*(++str);
  if ((c == '$') || (c == '(')) str++;
  if ((c == 'K') || (c == '$')) *esc_in = TRUE;
  else *esc_in = FALSE;

  if(*str != '\0') str++;
  return str;
}


/* ----------------------------------------------- JIS ¤ESJIS ¤ËÊÑ´¹¤¹¤E-- */

static void _seven2shift(unsigned char *str, unsigned char *str2)
{
  int p1, p2, esc_in = FALSE;

  while ((p1 = (int)*str) != '\0') {

    /* ESC¥·¡¼¥±¥ó¥¹¤ò¥¹¥­¥Ã¥×¤¹¤E*/
    if (p1 == ESC) {
      str = _skip_esc(str, &esc_in);
      continue;
    }

    if (p1 == LF || p1 == CR) {
      if (esc_in) esc_in = FALSE;
    }

    if(esc_in) { /* ISO-2022-JP ¥³¡¼¥É */
      if((p2 = (int)*(++str)) == '\0') break;

      _jis_shift(&p1, &p2);

      CHAROUT(p1);
      CHAROUT(p2);
    }else{       /* ASCII ¥³¡¼¥É */
      CHAROUT(p1);
    }
    str++;
  }
  *str2 = '\0';
}

/* ------------------------------------------------ JIS ¤EEUC ¤ËÊÑ´¹¤¹¤E-- */

static void _seven2euc(unsigned char *str, unsigned char *str2)
{
  int p1, esc_in = FALSE;

  while ((p1 = (int)*str) != '\0') {

    /* ESC¥·¡¼¥±¥ó¥¹¤ò¥¹¥­¥Ã¥×¤¹¤E*/
    if (p1 == ESC) {
      str = _skip_esc(str, &esc_in);
      continue;
    }

    if (p1 == LF || p1 == CR) {
      if (esc_in) esc_in = FALSE;
    }

    if(esc_in) { /* ISO-2022-JP ¥³¡¼¥É */
      CHAROUT(p1 + 128); 
      
      if((p1 = (int)*(++str)) == '\0') break;
      CHAROUT(p1 + 128);
    }else{       /* ASCII ¥³¡¼¥É */
      CHAROUT(p1);
    }
    str++;
  }
  *str2 = '\0';
}

/* ------------------------------------------------------------------------ */
/* --------------------------------------------------------- Public ´Ø¿E-- */
char *toStringJIS(char *str, char *buf, int maxlen) {
  int detected;

  if(!str) return (NULL);
  detected = detectKanjiCode(str);
  if(detected == ASCII || detected == JIS)
    return strncpy(buf, str, maxlen);

  if (maxlen < strlen(str) * 2) return NULL;

  switch(detected) {
  case SJIS :
    _shift2seven((unsigned char *)str, (unsigned char *)buf);
    break;
  case EUC :
    _euc2seven((unsigned char *)str, (unsigned char *)buf);
    break;
  default:
    return strncpy(buf, str, maxlen);
    break;
  }
  return buf;
}

char *toStringEUC(char *str, char *buf, int maxlen) {
  int detected;

  if(!str) return (NULL);
  detected = detectKanjiCode(str);
  if(detected == ASCII || detected == EUC) 
    return strncpy(buf, str, maxlen);

  if (maxlen < strlen(str) * 2) return NULL;

  switch(detected) {
  case SJIS :
    _shift2euc((unsigned char *)str, (unsigned char *)buf);
    break;
  case JIS :
  case NEW : case OLD : case NEC :
     _seven2euc((unsigned char *)str, (unsigned char*)buf);
    break;
  default:
    return strncpy(buf, str, maxlen);
    break;
  }
  return buf;
}

char *toStringSJIS(char *str, char *buf, int maxlen) {
  int detected;

  if (!str) return NULL;
  detected = detectKanjiCode(str);
  if(detected == ASCII)
    return strncpy(buf, str, maxlen);
  
  if (maxlen < strlen(str) * 2) return NULL;

  switch(detected) {
  case NEW : case OLD : case NEC :
  case JIS :
    _seven2shift((unsigned char *)str, (unsigned char *)buf);
    break;
  case EUC :
    _euc2shift((unsigned char *)str, (unsigned char *)buf);
    break;
  case SJIS :  
  default:
    _shift_self((unsigned char *)str, (unsigned char *)buf);
  }
  return buf;
}

char *toStringAuto(char *str, char *buf, int maxlen) {
  static int  jpcode = -1;
  static char *sjis_locale_name[] = {SJIS_LOCALE_NAME, NULL};
  static char *jis_locale_name[]  = {JIS_LOCALE_NAME, NULL};
  static char *euc_locale_name[]  = {EUC_LOCALE_NAME, NULL};
  static struct LOCALETABLE {
    int code;
    char **name_list;
  } locale_table[] = { {SJIS, sjis_locale_name},
		     {EUC, euc_locale_name},
		     {JIS, jis_locale_name}};

  if(!str) return (NULL);

  if (jpcode == -1) {
    char *ctype = setlocale(LC_CTYPE, "");
    int i, j;
    for( j=0; jpcode == -1 && 
	      j < sizeof(locale_table)/sizeof(struct LOCALETABLE); j++ ) {
      char **name = locale_table[j].name_list;
      for( i=0; name[i]; i++ )
	if (strcasecmp(ctype, name[i]) == 0) {
	  jpcode = locale_table[j].code;
	  break;
	}
    }
    if(jpcode == -1)
        jpcode = ASCII;
  }

  switch (jpcode) {
    case SJIS:
      return (toStringSJIS(str, buf, maxlen));
    break;
    case JIS:
    case NEW : case OLD : case NEC :
      return (toStringJIS(str, buf, maxlen));
    break;
    case EUC:
      return (toStringEUC(str, buf, maxlen));
    break;
    default:
      return (strncpy(buf, str, maxlen));
    break;
  }
}

char *EUCtoSJIS(char *str, char *buf, int maxlen)
{
  if (!str) return NULL;
  _euc2shift((unsigned char *)str, (unsigned char *)buf);
  return buf;
}
