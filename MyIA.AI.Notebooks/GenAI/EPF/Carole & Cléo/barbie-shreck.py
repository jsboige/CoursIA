#Projet : "Barbie vs Âne de Shrek – Le Duel Verbal Contraint"
#Objectif : Simuler un débat humoristique où Barbie et l'Âne de Shrek argumentent en respectant une contrainte linguistique et génèrent une image après chaque échange.

#Installation et Imports
# Installation des bibliothèques nécessaires


# Import des bibliothèques
import os
import logging
import random
from dotenv import load_dotenv
from semantic_kernel import Kernel
from semantic_kernel.agents import ChatCompletionAgent, AgentGroupChat
from semantic_kernel.agents.strategies.termination.termination_strategy import TerminationStrategy
from semantic_kernel.connectors.chat.open_ai import OpenAIChatCompletion
from semantic_kernel.contents import ChatHistory, ChatMessageContent, AuthorRole
from semantic_kernel.functions import KernelArguments
from dalle import text2im  # Utilisation de DALL-E pour générer les images

# Chargement des variables d'environnement
load_dotenv()

# Configuration des logs
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler()]
)
logger = logging.getLogger("BarbieVsAne")

# Création du kernel
def create_kernel():
    kernel = Kernel()
    kernel.add_service(OpenAIChatCompletion(
        service_id="openai",
        ai_model_id="gpt-4o-mini",
        api_key=os.getenv("OPENAI_API_KEY")
    ))
    return kernel


#Définition des Contraintes Linguistiques
CONTRAINTES = [
    "Rime obligatoire",
    "Style poétique",
    "Nombre de mots limité",
    "Mode Shakespeare",
    "Alphabet contraint",
    "Réplique en chanson"
]

# Sélection aléatoire d'une contrainte
def choisir_contrainte():
    return random.choice(CONTRAINTES)

#Définition des Prompts des Personnages
# Définition des personnages et de leurs instructions
BARBIE_PROMPT = """
Tu es Barbie, élégante et sophistiquée. 
Tu dois débattre avec l’Âne de Shrek sur des sujets variés. 
Ta réponse doit respecter la contrainte suivante : {contrainte}.
Garde un ton inspirant et raffiné.
"""

ANE_SHREK_PROMPT = """
Tu es l’Âne de Shrek, plein d’humour et d'énergie ! 
Tu dois répondre à Barbie de manière comique et spontanée.
Ta réponse doit respecter la contrainte suivante : {contrainte}.
Sois drôle et imprévisible !
"""
#Création des Agents
def creer_agent(nom, prompt):
    return ChatCompletionAgent(
        kernel=create_kernel(),
        service_id="openai",
        name=nom,
        instructions=prompt
    )

# Création des agents avec une contrainte aléatoire
contrainte = choisir_contrainte()
barbie = creer_agent("Barbie", BARBIE_PROMPT.format(contrainte=contrainte))
ane_shrek = creer_agent("Ane_Shrek", ANE_SHREK_PROMPT.format(contrainte=contrainte))

# Stratégie de Terminaison
class BarbieAneTerminationStrategy(TerminationStrategy):
    """Arrête la partie après un nombre limité d'échanges."""
    
    MAX_ITERATIONS = 10  # Nombre d'échanges maximum
    
    async def should_terminate(self, agent, history, cancellation_token=None):
        return len(history) >= self.MAX_ITERATIONS

# Génération d’Images après Chaque Réplique
def extraire_mots_cles(texte):
    """Sélectionne les mots-clés pour générer une image."""
    mots = texte.split()
    return " ".join(random.sample(mots, min(3, len(mots))))  # 3 mots-clés max

async def generer_image(texte):
    """Génère une image basée sur les mots-clés extraits de la réponse."""
    mots_cles = extraire_mots_cles(texte)
    image = text2im({"prompt": f"Illustration de {mots_cles}", "size": "1024x1024"})
    return image
#Lancement du Débat
async def jouer_partie():
    logger.info("🎭 Début du duel Barbie vs Âne de Shrek !")
    logger.info(f"🌀 Contrainte sélectionnée : {contrainte}")
    
    # Configuration du chat groupé
    chat = AgentGroupChat(
        agents=[barbie, ane_shrek],
        termination_strategy=BarbieAneTerminationStrategy()
    )
    
    async for message in chat.invoke():
        role = message.role
        logger.info(f" [{role}] : {message.content}")
        
        # Génération d'une image pour chaque réplique
        image = await generer_image(message.content)
        logger.info(f"🖼️ Image générée : {image}")
    
    logger.info("🏁 Partie terminée !")

# Exécuter la partie
import asyncio

# Vérifier si le script est exécuté directement
if __name__ == "__main__":
    asyncio.run(jouer_partie())
