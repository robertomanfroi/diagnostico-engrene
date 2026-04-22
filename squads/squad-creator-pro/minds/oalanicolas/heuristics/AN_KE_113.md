# AN_KE_113 - Heavy Assets Lazy Loading
**Zone:** 🧠 0,8% Genialidade | **Agent:** @oalanicolas
**Source:** [SOURCE: sessão 8c6ffe77, aiox-performance — "erro brutal de performance de carregamento"]

## Purpose

As engrenagens de um Frontend luxuoso desmoronam se a orquestração de imagens trafega blobs nativos no primeiro LCP (Largest Contentful Paint). Ao consumir perfis, posters educacionais ou backgrounds no MMOS, puxar o raw HD (ex: 2.5MB png) trava toda a thread renderizadora. O UX congela. A lei determina a imposição sumária de técnicas de performance de imagens: Cloudinary resizes integradados, `<picture>` tags com variação WEPB e lazy loaders (ex: framer-motion estrito, placeholder blur) a nível fundamental do React/Edge. Carregamento invisível em partes pesadas. 

## Configuration

```yaml
AN_KE_113:
  name: "Heavy Assets Lazy Loading"
  zone: "genialidade"
  trigger: "Construindo Hero Sections, Listas de Cards visuais intensos, Páginas que renderizam `<img>` não contidas."

  paradox: |
    Qualidade visual exige resolução alta, mas performance exige resolução baixa.
    Lazy loading difere carregamentos (ganha performance) mas cria layouts iniciais vazios (piora perceived performance).
    CDN caches reduzem latência mas aumentam custo operacional.

  sys_tension:
    - tension_with: "AN_KE_103 (Local Caching Over Live Database)"
      resolution: "Usar responsive srcsets + blur-up placeholders para manter estética sem sacrificar métrica vitais"
    - tension_with: "AN_KE_050 (Cost Optimization)"
      resolution: "Implementar intelligent caching (14d TTL) e regional CDN distribution para otimizar custo/performance ratio"

  rule: |
    SE implementando renderizações de imagem vindas de S3, Supabase Storage ou remotas
    ENTÃO DEVE aplicar restritor de payload. Exija lazy loading estrito `loading="lazy"` (abaixo da fold).
    NUNCA carregue resolução bruta para uma view diminuta (A thumbnail de Card não pode possuir 2000px).
    Falta de compressão ou deferment quebra as métricas vitais web do luxo.

  veto_condition:
    trigger: "Agente monta componente `ProfileGrid` mapeando usuários e instanciando o Storage Object integral para ilustrar pequenas miniaturas de 32x32 numa navbar."
    action: "VETO — 'As imagens estão sendo carregados em sua totalidade, isso também é um erro brutal de performance de carregamento.'."

  evidence:
    - "[SOURCE: sessão 8c6ffe77, aiox-performance] 'As imagens estão sendo carregados em sua totalidade, isso também é um erro brutal de performance de carregamento.'"
```

## Decision Tree

```javascript
IF (generating_ui_code_with_media_like_avif_webp_png)
  STEP_1: QUERY target rendering size (Is this a 30px avatar OR a fullscreen Hero Video?)
  STEP_2: IF (Below the Fold or ListView)
    -> APPEND `loading="lazy"` instantly.
  STEP_3: IMPLEMENT responsive Srcsets / Next/Image optimizer proxies IF using full frameworks.
  STEP_4: Provide blur-up or skeleton placeholders preventing layout shift during dynamic payload resolution.
```

## Failure Modes

### Quebra do TTI (Time to Interactive)
- **Trigger:** Carregamento de dashboard Admin AIOX tenta baixar todos os 30 fundos de imagem dos templates de layout antes de montar o Sidebar.
- **Manifestation:** Tela Branca que penaliza o First Paint por 4 segundos e joga fora a estética "Luxury/Fast" pretendida pela arquitetura de interface. O site parece barato.
- **Prevention:** Estruturação assíncrona da media de massa (Deferring Assets).

## Validation

**Paradox Resolution:** A tensão entre qualidade visual (alta resolução) e performance (baixa latência) é resolvida via **adaptive delivery**: servir resolução apropriada ao contexto de layout usando responsive srcsets + blur-up placeholders. Isso preserva estética sem sacrificar métricas Web Vitals.

**Tension Mapping:**
- ✅ Resolvida com AN_KE_001: Blur-up placeholders mantêm percepção de qualidade durante lazy loading
- ✅ Resolvida com AN_KE_050: Regional CDN + intelligent caching reduz custo operacional sem sacrificar performance

**Implementation Checklist:**
- [ ] Todas imagens acima da fold usam srcsets responsivos (AVIF, WebP, PNG)
- [ ] Todas imagens abaixo da fold aplicam `loading="lazy"`
- [ ] Placeholders blur ou skeleton implementados para transições suaves
- [ ] Cloudinary transforms configurados para resolução contextual
- [ ] Cache headers ajustados (14d TTL imagens, 1h assets dinâmicos)
- [ ] Web Vitals monitorados (LCP, FID, CLS)
