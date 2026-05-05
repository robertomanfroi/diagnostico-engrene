FROM node:20-slim

# Instalar dependências de sistema (ffmpeg, python3, pip, curl)
RUN apt-get update && apt-get install -y --no-install-recommends \
    ffmpeg \
    python3 \
    python3-pip \
    python3-venv \
    curl \
    ca-certificates \
  && rm -rf /var/lib/apt/lists/*

# Instalar yt-dlp
RUN curl -L https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp \
    -o /usr/local/bin/yt-dlp && chmod a+rx /usr/local/bin/yt-dlp

# Instalar pacotes Python (opcional — não falha o build se indisponível)
RUN pip3 install --break-system-packages instagrapi instaloader 2>/dev/null || true

WORKDIR /app

# Instalar dependências Node
COPY package*.json ./
RUN npm ci --only=production

# Copiar código
COPY . .

EXPOSE 3000

CMD ["node", "server.js"]
