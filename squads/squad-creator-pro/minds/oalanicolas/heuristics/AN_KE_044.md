---
heuristic_id: AN_KE_044
name: "URL = State Truth (Deep Linking)"
zone: excelencia
type: "Architecture UI/UX Heuristic"
agent: "@oalanicolas"
pattern: "React & JS State vs Browser History"
sys_tension:
  tension_with: "AN_KE_103 (Local Caching Over Live Database)"
  resolution: "Lazy-load state from URL params on mount; cache parsed state in React memory for perf; invalidate on URL change"
source: |
  Frustrações expressas com componentes que aprisionam o "State" localmente e quebram as premissas primárias do "Browser" (foward, back, refresh). Refatorações em Dashboards e Lojas de Cursos.
---

# AN_KE_044 - URL = State Truth (Deep Linking)

**Type:** Architecture UI/UX Heuristic
**Zone:** 💎 4% Excelência
**Agent:** @oalanicolas
**Pattern:** React & JS State vs Browser History
**Source:** [SOURCE: Frustrações expressas com componentes que aprisionam o "State" localmente e quebram as premissas primárias do "Browser" (foward, back, refresh). Refatorações em Dashboards e Lojas de Cursos.]

## Purpose

Assegurar acessibilidade profunda em projetos web complexos. Quando listas compridas, filtros ou abas vivem apenas em um `useState` em React sem reflexos na URL do browser (e.g. `?tab=cursos&page=2`), o usuário perde anos de memória celular de navegação web (refresh destrói as tabs ativas).

## Configuration

```yaml
AN_KE_044:
  name: "URL = State Truth (Deep Linking)"
  zone: "excelencia"
  trigger: "Construindo gerenciamento de estado em UIs complexas (Listas, Filtros, Tabs, Paineis modais extensos ou Breadcrumbs)."

  rule: |
    SE você implementar a gestão de estado central de um componente pesado de navegação
    ENTÃO ele DEVE modificar dinamicamente a URL usando searchParams ou Pathing Slug.
    A URL dita quem é o State do aplicativo; NUNCA deixe estado trancado na caixinha de memória da página, se o usuário der refresh, a página não deve resetar misteriosamente para o estado zero.

  veto_condition:
    trigger: "Criar uma tabela enorme de usuários com React Data Table onde filtrar `name=john` não altera o query da URL em cima."
    action: "VETO — Amarre os gatilhos ao useSearchParams / history Push para resiliência de recarregamento (F5) impecável."

  evidence:
    - "[EXACT WORDS]: Eu quero que o sistema funcione modifiquendo também a URL, assim pode voltar para mesma página sem precisar navegar até ela sempre que entrar."
```

## Decision Tree

```javascript
IF (creating_filter OR implementing_tabs_panel OR page_pagination)
  IF (state_management_is_exclusively_local_memory == TRUE)
    // Only uses React hooks like `const [activeTab, setActiveTab] = useState()`
    THEN INITIATE_VETO
    THEN REQUIRE_URL_SYNCHRONIZATION ("Refatore para usar next/compat ou Router Hooks injetando '?tab=X' na URI da aba e a tela leia essa fonte da verdade.")
      IF (State is successfully extracted from URI)
        THEN proceed cleanly. (User can bookmark the current filtered setup)
  ELSE
    // Standard approach of Web Routing
    THEN ALLOW_PRODUCTION
```

## Failure Modes

### Amnésia Total por Refresh
- **Trigger:** Após aplicar 5 complexos dropdown filters e selecionar arquivos em um checklist massivo de cursos dentro da URL raiz.
- **Manifestation:** O usuário clica em "Detalhes do Produto" em nova aba. Em seguida, erra o clique no histórico ("back"). Todos os 5 filtros somem. A página retorna estúpida.
- **Detection:** Reclamações frustrantes de clientes pedindo que o sistema lembre deles.
- **Recovery:** Re-codificar a máquina de estados (React Query etc.) atrelando puramente search params.
- **Prevention:** Exigência no prompt de design de UX "Todas as escolhas não efêmeras de navegação devem gerar hashes de URL".

## Integration with Workflow

```yaml
checkpoint:
  id: "state-lives-in-url"
  heuristic: AN_KE_044
  phase: "Frontend_Component_Creation"
```

## Validation

**Acceptance Criteria:**
- [ ] All filterable/navigable state is present in URL searchParams or path slug
- [ ] Refresh (F5) preserves the exact UI state without loss of context
- [ ] Browser back/forward buttons correctly traverse the state history
- [ ] Bookmarkable URLs resolve to the exact same component state
- [ ] Performance is not degraded (cached state in React; lazy-load from URL on mount only)

**Test Case:**
1. Apply 5 complex filters + select items in a checklist
2. Refresh the page (F5)
3. Verify all filters and selections remain intact
4. Verify URL contains all state parameters
5. Copy URL, open in new tab, verify identical state loads

**Resolution:** If state is lost on refresh or URL does not reflect UI state, apply VETO and refactor using `useSearchParams()` (Next.js) or `useLocation/history` (React Router) to synchronize state bidirectionally with the browser URL.
