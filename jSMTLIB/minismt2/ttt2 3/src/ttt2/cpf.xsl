<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  version="1.0">
  <xsl:output method="xml" indent="yes"/>
  <xsl:strip-space elements="*"/>

<xsl:template match="/certificationProblem">
  <xsl:processing-instruction name="xml-stylesheet">type="text/xsl" href="cpfHTML.xsl"</xsl:processing-instruction>
  <xsl:copy>
    <xsl:copy-of select="@*"/>
    <xsl:apply-templates/>
  </xsl:copy>
</xsl:template>

<xsl:template match="bounds">
  <xsl:copy>
    <xsl:apply-templates select="type"/>
    <xsl:apply-templates select="bound"/>
    <xsl:apply-templates select="finalStates"/>
    <xsl:apply-templates select="treeAutomaton"/>
    <xsl:apply-templates select="relation"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="subtermProc">
  <xsl:copy>
    <xsl:apply-templates select="argumentFilter"/>
    <xsl:apply-templates select="dps"/>
    <xsl:apply-templates select="dpProof"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="dpTrans">
  <xsl:copy>
    <xsl:apply-templates select="dps"/>
    <xsl:apply-templates select="markedSymbols"/>
    <xsl:apply-templates select="dpProof"/>
  </xsl:copy>
</xsl:template>
  
<xsl:template match="signature">
  <signature>
    <xsl:for-each select="symbol">
      <symbol>
        <xsl:apply-templates/>
      </symbol>
    </xsl:for-each>
  </signature>
</xsl:template>

<xsl:template match="symbol">
  <xsl:call-template name="symbol">
    <xsl:with-param name="args" select="*"/>
  </xsl:call-template>
</xsl:template>

<xsl:template name="symbol">
  <xsl:param name="args"/>
  <xsl:choose>
    <xsl:when test="count($args) = 1">
      <xsl:copy-of select="$args[1]"/>
    </xsl:when>
    <xsl:when test="$args[last()] = sharp">
      <sharp>
        <xsl:call-template name="symbol">
          <xsl:with-param name="args" select="$args[position() != last()]"/>
        </xsl:call-template>
      </sharp>
    </xsl:when>
    <xsl:when test="$args[last()] = numberLabel">
      <labeledSymbol>
        <xsl:call-template name="symbol">
          <xsl:with-param name="args" select="$args[position() != last()]"/>
        </xsl:call-template>
        <numberLabel>
        <xsl:apply-templates select="$args[last()]/*"/>
        </numberLabel>
      </labeledSymbol>
    </xsl:when>
    <xsl:when test="$args[last()] = symbolLabel">
      <labeledSymbol>
        <xsl:call-template name="symbol">
          <xsl:with-param name="args" select="$args[position() != last()]"/>
        </xsl:call-template>
        <symbolLabel>
        <xsl:apply-templates select="$args[last()]/*"/>
        </symbolLabel>
      </labeledSymbol>
    </xsl:when>
    <xsl:otherwise/>
  </xsl:choose>
</xsl:template>

<xsl:template name="redPairProc">
  <xsl:param name="UR"/>
  <xsl:param name="P"/>
  <xsl:choose>
    <xsl:when test="$P/usableRules/rules and count($P/usableRules/rules) > 0">
      <redPairUrProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <xsl:apply-templates select="$P/usableRules"/>
        <xsl:apply-templates select="$P/*[last()]"/>
      </redPairUrProc>
    </xsl:when>
    <xsl:when test="$UR and count($UR) > 0">
      <redPairUrProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <usableRules>
          <xsl:apply-templates select="$UR"/>
        </usableRules>
        <xsl:apply-templates select="$P/*[last()]"/>
      </redPairUrProc>
    </xsl:when>
    <xsl:otherwise>
      <redPairProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <xsl:apply-templates select="$P/*[last()]"/>
      </redPairProc>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="redPairProc">
  <xsl:call-template name="redPairProc">
    <xsl:with-param name="P" select="current()"/>
  </xsl:call-template>
</xsl:template>

<xsl:template name="monoRedPairProc">
  <xsl:param name="UR"/>
  <xsl:param name="P"/>
  <!--<dpProof>-->
  <xsl:choose>
    <xsl:when test="$P/usableRules/rules and count($P/usableRules/rules) > 0">
      <monoRedPairUrProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <xsl:apply-templates select="$P/trs"/>
        <xsl:apply-templates select="$P/usableRules"/>
        <xsl:apply-templates select="$P/*[last()]"/>
      </monoRedPairUrProc>
    </xsl:when>
    <xsl:when test="$UR and count($UR) > 0">
      <monoRedPairUrProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <xsl:apply-templates select="$P/trs"/>
        <usableRules>
          <xsl:apply-templates select="$UR"/>
        </usableRules>
        <xsl:apply-templates select="$P/*[last()]"/>
      </monoRedPairUrProc>
    </xsl:when>
    <xsl:otherwise>
      <monoRedPairProc>
        <xsl:apply-templates select="$P/orderingConstraintProof"/>
        <xsl:apply-templates select="$P/dps"/>
        <xsl:apply-templates select="$P/trs"/>
        <xsl:apply-templates select="$P/*[last()]"/>
      </monoRedPairProc>
    </xsl:otherwise>
  </xsl:choose>
  <!--</dpProof>-->
</xsl:template>

<xsl:template match="monoRedPairProc">
  <xsl:call-template name="monoRedPairProc">
    <xsl:with-param name="P" select="current()"/>
  </xsl:call-template>
</xsl:template>

<xsl:template match="usableRulesProc">
  <xsl:choose>
    <xsl:when test="./dpProof/redPairProc">
      <xsl:call-template name="redPairProc">
        <xsl:with-param name="UR" select="./trs/rules"/>
        <xsl:with-param name="P" select="./dpProof/redPairProc"/>
      </xsl:call-template>
    </xsl:when>
    <xsl:when test="./dpProof/monoRedPairProc">
      <xsl:call-template name="monoRedPairProc">
        <xsl:with-param name="UR" select="./trs/rules"/>
        <xsl:with-param name="P" select="./dpProof/monoRedPairProc"/>
      </xsl:call-template>
    </xsl:when>
    <xsl:otherwise/>
  </xsl:choose>
</xsl:template>

<xsl:template match="dpProof">
  <xsl:choose>
    <xsl:when test="restore">
      <xsl:apply-templates select="./restore/dpProof"/>
    </xsl:when>
    <xsl:when test="depGraphProc
      and count(./depGraphProc/component) = 0
      and ./depGraphProc/dpProof/*[name() != 'pIsEmpty']">
      <xsl:apply-templates select="./depGraphProc/dpProof"/>
    </xsl:when>
    <xsl:otherwise>
      <xsl:copy><xsl:apply-templates/></xsl:copy>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="depGraphProc">
  <xsl:choose>
    <xsl:when test="./dpProof/pIsEmpty">
      <xsl:copy>
        <xsl:for-each select="./dps/rules/rule">
          <component>
            <dps>
              <rules>
                <xsl:apply-templates select="."/>
              </rules>
            </dps>
            <realScc>false</realScc>
          </component>
        </xsl:for-each>
      </xsl:copy>
    </xsl:when>
    <xsl:otherwise>
      <xsl:copy>
        <xsl:apply-templates/>
      </xsl:copy>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="crKB">
  <wcrAndSN>
    <wcrProof>
      <joinableCriticalPairsAuto/>
    </wcrProof>
    <xsl:apply-templates select="trsTerminationProof"/>
  </wcrAndSN>
</xsl:template>

<xsl:template match="trsConfluenceProof">
  <xsl:copy-of select="@*"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="dcrProof">
  <xsl:copy-of select="@*"/>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="trsTerminationProof">
  <xsl:choose>
    <xsl:when test="count(cpTrans) != 0">
      <xsl:apply-templates select="cpTrans/complexityProof"/>
    </xsl:when>
    <xsl:when test="count(crProof) != 0">
      <xsl:apply-templates/>
    </xsl:when>
    <xsl:otherwise>
      <xsl:copy>
        <xsl:copy-of select="@*"/>
        <xsl:apply-templates/>
      </xsl:copy>      
    </xsl:otherwise>
  </xsl:choose>  
</xsl:template>

<xsl:template match="trsNonterminationProof">
  <xsl:choose>
    <xsl:when test="count(crDisproof) != 0">
      <xsl:apply-templates/>
    </xsl:when>
    <xsl:otherwise>
      <xsl:copy>
        <xsl:copy-of select="@*"/>
        <xsl:apply-templates/>
      </xsl:copy>      
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="*">
  <xsl:copy>
    <xsl:copy-of select="@*"/>
    <xsl:apply-templates/>
  </xsl:copy>
</xsl:template>

</xsl:stylesheet>
