FROM node:20-slim

# Instalar dependências do sistema
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    python3-venv \
    ffmpeg \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Instalar yt-dlp
RUN curl -L https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp -o /usr/local/bin/yt-dlp \
    && chmod a+rx /usr/local/bin/yt-dlp

# Instalar pacotes Python
RUN pip3 install --break-system-packages instaloader instagrapi

WORKDIR /app

# Copiar package.json e instalar dependências Node
COPY package*.json ./
RUN npm ci --only=production

# Copiar o restante do projeto (exceto node_modules e .env)
COPY . .

EXPOSE 3000

CMD ["node", "server.js"]
