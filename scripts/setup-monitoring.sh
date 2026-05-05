#!/bin/bash
# Setup UptimeRobot monitoring para diagnostico-engrene
# Uso: UPTIMEROBOT_API_KEY=xxx bash scripts/setup-monitoring.sh

set -e

URL="https://diagnostico-engrene-production.up.railway.app"
HEALTH_URL="${URL}/health"
API_KEY="${UPTIMEROBOT_API_KEY:-}"

if [ -z "$API_KEY" ]; then
  echo "⚠️  UPTIMEROBOT_API_KEY não definida. Cadastre em https://uptimerobot.com"
  echo "   Depois: UPTIMEROBOT_API_KEY=sua_key bash scripts/setup-monitoring.sh"
  exit 1
fi

echo "🔍 Criando monitor UptimeRobot para: $HEALTH_URL"

RESPONSE=$(curl -s -X POST "https://api.uptimerobot.com/v2/newMonitor" \
  -H "Content-Type: application/x-www-form-urlencoded" \
  --data-urlencode "api_key=${API_KEY}" \
  --data-urlencode "format=json" \
  --data-urlencode "type=1" \
  --data-urlencode "url=${HEALTH_URL}" \
  --data-urlencode "friendly_name=Diagnostico Engrene - Health" \
  --data-urlencode "interval=300" \
  --data-urlencode "alert_contacts=")

echo "Resposta: $RESPONSE"

STATUS=$(echo "$RESPONSE" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d.get('stat','?'))")
if [ "$STATUS" = "ok" ]; then
  echo "✅ Monitor criado com sucesso! Verificação a cada 5 minutos."
else
  echo "❌ Erro ao criar monitor. Verifique a API key."
fi
