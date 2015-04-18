// thanks to Simon and Tom
#include <stdio.h>
#include <string.h>
#include <libxslt/xslt.h>
#include <libxslt/xsltInternals.h>
#include <libxslt/transform.h>
#include <libxslt/xsltutils.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

#include "cpf.xsl.h"
#include "html.xsl.h"

#ifndef XML_PARSE_HUGE
/* older versions of libxml2 did not support XML_PARSE_HUGE */
# define XML_PARSE_HUGE 0
#endif

struct xsl_info {
	unsigned char* xsl;
	int xsl_len;
} typedef xsl_info;

CAMLprim value transform(value input, xsl_info** xsls, int xsls_len) {
	const char* xml = String_val(input);
	const char** params = {NULL};

	xsltStylesheetPtr style;
	xmlDocPtr doc_style, doc, doc_old;

	//doc = xmlParseMemory(xml, strlen(xml));
	doc = xmlReadMemory(xml, strlen(xml), NULL, NULL, XML_PARSE_HUGE);

	int i;
	for (i = 0; i < xsls_len; i++) {
		doc_old = doc;
		xsl_info* x = xsls[i];
		//doc_style = xmlParseMemory((const char*)x->xsl, x->xsl_len);
		doc_style = xmlReadMemory((const char*)x->xsl, x->xsl_len, NULL, NULL, XML_PARSE_HUGE);
		style = xsltParseStylesheetDoc(doc_style);
		doc = xsltApplyStylesheet(style, doc, params);
		xsltFreeStylesheet(style);
		xmlFreeDoc(doc_old);
	}

	xmlChar* s;
	int len;
	style = xsltNewStylesheet();
	xsltSaveResultToString(&s, &len, doc, style);
  xsltFreeStylesheet(style);

	xmlFreeDoc(doc);
	xsltCleanupGlobals();
	xmlCleanupParser();

	value r = caml_copy_string((char*) s);
	free(s);
	return r;
}

CAMLprim value cpf(value input) {
	xsl_info cpf = {cpf_xsl, cpf_xsl_len};
	xsl_info* xsls[] = {&cpf};
	return transform(input, xsls, 1);
}

CAMLprim value cpf_html(value input) {
	xsl_info cpf = {cpf_xsl, cpf_xsl_len};
	xsl_info html = {html_xsl, html_xsl_len};
	xsl_info* xsls[] = {&cpf, &html};
	return transform(input, xsls, 2);
}
