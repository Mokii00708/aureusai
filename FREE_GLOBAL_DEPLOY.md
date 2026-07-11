# Free Global Deployment (No Money)

This project is prepared for **Render Free Web Service**.

## What you get
- Public HTTPS URL reachable internationally.
- No tunnel expiration every hour.
- Zero cost (free tier).

## Important free-tier notes
- Service can "sleep" after inactivity and wake on first request.
- Local file storage is ephemeral on restarts/redeploys.
  - Files under `data/` and `history.json` can reset.
  - For persistent memory long-term, later connect a free hosted database.

## One-time setup
1. Push this folder to a GitHub repository.
2. Open Render dashboard and click **New + > Blueprint**.
3. Select your GitHub repo.
4. Render will detect `render.yaml` automatically.
5. Add environment variable:
   - `OPENAI_API_KEY` = your real API key
6. Deploy.

### Fast GitHub push commands
```bash
git init
git add .
git commit -m "Prepare free global deployment"
git branch -M main
git remote add origin https://github.com/<your-user>/<your-repo>.git
git push -u origin main
```

## URLs after deploy
- Presentation: `https://<your-render-domain>/`
- Chat: `https://<your-render-domain>/chat`

## Included config files
- `requirements.txt`
- `render.yaml`

## Local run (unchanged)
```bash
OPENAI_API_KEY=your_key HOST=0.0.0.0 PORT=5004 FLASK_DEBUG=0 python3 app.py
```
