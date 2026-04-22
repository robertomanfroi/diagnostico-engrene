---
id: "PV_KE_068"
title: "O Vínculo de Sangue (Unidirectional Root-Derived Inheritance)"
mind: "pedro_valerio"
type: "heuristics"
tags:
  - "Data Normalization"
  - "Composition Rules"
pipeline_instances:
  - "hybrid-ops"
sys_tension:
  tension_with: "PV_KE_032 (Schema Immutability) vs Herança Fluida"
  resolution: "Herança unidirecional aplica-se a Dados Operacionais Vivos. Documentos históricos/legais ativam Deep Freeze no ponto de handoff, quebrando o vínculo de herança e congelando valores retroativamente imutáveis."
---

# PV_KE_068 - O Vínculo de Sangue (Unidirectional Root-Derived Inheritance)

**Type:** Decision Heuristic
**Zone:** 🧠 4% Expert Insight | **Agent:** @hybridOps:data-engineer
**Source:** [SOURCE: SINKRA-v4.md | Capítulo 11: O 5º Mecanismo: Herança]

## Purpose
Excluir o retrabalho de digitação redundante e a dissonância cognitiva de dados. A SINKRA não duplica informações atemporais, ela compartilha os vetores da Raiz Mãe. Se um `Contrato` (Entidade Derivada) compartilha o campo de "Segmento" com a `Empresa` (Entidade Raiz), ele é **Herdado** fisicamente do escopo primário e transmitido hierarquicamente. Copiar campos cria Divergência Silenciosa.

## Configuration
```yaml
PV_KE_068:
  name: "Unidirectional Field Inheritance Law"
  zone: "zone_4"
  trigger: "O usuário cadastra novamente o 'Plano de Assinatura' da Empresa nos detalhes do 'Ticket de Suporte' do mês de Abril."
  evidence_threshold: "database_normalization_axiom"
  rule: |
    SE uma propriedade (como 'Nome do Cliente' ou 'Tier') já existe na Entidade Root Primária
    ENTÃO Instâncias de Entidades Derivadas Dependentes devem APENAS possuir Referências Pointers `inherited_fields` linkados para lá. O Pai transmite. 
  veto_condition:
    trigger: "Criar uma automação Sync Bidirecional entre o Contrato e o Lead (Ambos alteram o Cnpj)."
    action: "VETO ESTRUTURAL. A herança só funciona De Raiz para O Derivado. Nunca o contrário. A ponta final nunca tem permissão para subscrever seu modelo central."
```

## Decision Tree
```javascript
IF (designing_a_schema_for_a_Derived_Entity_like_Contract_or_Ticket)
  STEP_1: COMPARE required fields against its Parent Root Entity (Company/Person).
    IF (Field_Already_Exists_in_Root && It_is_a_timeless_attribute)
      -> RULE: Register under `inherited_fields: Parent.Attribute`. Do NOT recreate the field.
    IF (Field_is_Local_Temporal_Status_of_the_Interaction_itself) // e.g. Contract Amount, Ticket Priority
      -> RULE: Register under `own_fields`. 
NEVER:
  Obrigar seus humanos a entrarem na aba de uma Tarefa Derivada e terem que alterar o telefone corporativo de um Lead só porque o campo duplicado ali ficou desatualizado ontem à noite.
```

## Failure Modes

### Misapplication / Excess: "O Dogma Estrito do Retrato (Snapshot Corrompido)"
- **Trigger:** Num cenário Legal Fiscal pesado, o sistema é inteiramente herdado. A fatura fiscal N° 90 de seis meses atrás simplesmente "herda por link" o Endereço atual do Cliente (Company Root). O cliente muda de endereço na Sede Nacional.
- **Manifestation:** A fatura N° 90 de seis meses atrás milagrosamente se auto-atualiza e muda de cidade impressa. Na auditoria fiscal, o governo processa a empresa por Falsa Emissão Retrospectiva, as defesas caem pois o PDF dinâmico foi mutado por conta de uma "Herança" mal interpretada no frontend.
- **Detection:** Documentos que necessitam ser imutáveis e congelados no passado oscilando seus valores baseados em atualizações contemporâneas.
- **Recovery:** A Lei da Herança serve para Dados Operacionais Vivos Correntes. Quando os outputs são Documentos Passíveis de Lei (e.g., Faturas, Registros Fiscais), eles exigem o uso do Pattern `Deep Freeze Snapshot` gerado no Handoff, que quebra o cordão umbilical de herança naquele milissegundo final da instância.
- **Prevention:** Discernimento ativo entre Dado Fluido Atemporal vs Artefato Histórico Congelado.

### Omission / Failure to Activate: "O Hospício dos Mil Cadastros"
- **Trigger:** O time de Vendas e o time de Operações criam suas pastas. Cada software ou pipeline tem seu Field chamado "Level de SLA do Cliente" que o comercial deve preencher na mão em cada instância que abre para a conta.
- **Manifestation:** O cliente sofre Downgrade Financeiro na raiz porque parou de pagar o Plano Pro. Mas como Operações continua lendo o Card duplicado na Pipeline deles que diz `SLA: Pro`, a máquina despacha 40 tickets em alta velocidade por uma semana. Custo torrado, desalinhamento bruto. 
- **Detection:** Reuniões onde dois analistas puxam a ficha do MESMO cliente e os campos de perfil relatam verdades totalmente opostas a depender de qual Pipeline extraíram a amostra.
- **Recovery:** O `Company.Level` é Root Base Privilegiada. Em Operations, as Instances invocam um Pointer Read-Only Atômico. Se mudar em Alfa, reflete em Omega, mantendo o Cosmos unificado e a verdade singular absoluta.

---

## Validation

**Checklist de Aplicação (PV_KE_068):**
- [ ] Schema mapeou campos atemporais vs. temporais da entidade derivada
- [ ] Campos atemporais (nome cliente, segmento, tier) usam `inherited_fields` pointer para Root
- [ ] Campos temporais locais (status, prioridade, valor contrato) registrados em `own_fields`
- [ ] Documentos legais/fiscais habilitam `deep_freeze: true` no handoff
- [ ] Testes verificam que mudança em Root propaga atomicamente para Derivados vivos
- [ ] Testes verificam que documentos congelados mantêm snapshot imutável apesar de Root mudar
- [ ] Bidireção explicitamente rejeitada via `veto_condition` em schema validation 
