<?php
/**
 * Seed de l'instance jetable « Maison Valmont ».
 *
 * Branche AI Engine sur un provider LLM local compatible OpenAI
 * (Ollama, vLLM, ...), active les modules et cree le chatbot « valmont ».
 * Cree aussi un mu-plugin qui autorise les application passwords sans HTTPS
 * (exigence WordPress 6.8 : wp_is_application_passwords_available).
 *
 * Usage (apres installation de WordPress et activation d'AI Engine, cf. README) :
 *
 *   docker cp seed-valmont.php valmont-wordpress_cli-1:/tmp/seed-valmont.php
 *   docker exec valmont-wordpress_cli-1 sh -c "php /tmp/seed-valmont.php"
 *
 * Variables d'environnement attendues (propagees par docker-compose depuis .env) :
 *   VALMONT_LLM_BASE_URL   endpoint OpenAI-compatible du LLM (ex: http://host.docker.internal:11434/v1)
 *   VALMONT_LLM_API_KEY    cle d'API (ou 'sk-local' pour un serveur local sans cle)
 *   VALMONT_LLM_MODEL      identifiant du modele (ex: qwen3.6-35b-a3b)
 *   VALMONT_LLM_MODEL_NAME libelle affiche dans l'interface
 *
 * L'URL exacte du provider ne doit JAMAIS etre ecrite en dur dans ce script :
 * elle passe par l'environnement. Rien dans ce fichier n'est un secret.
 */

require '/var/www/html/wp-load.php';

$base_url  = getenv('VALMONT_LLM_BASE_URL')  ?: 'http://host.docker.internal:11434/v1';
$api_key   = getenv('VALMONT_LLM_API_KEY')   ?: 'sk-local';
$model     = getenv('VALMONT_LLM_MODEL')     ?: 'qwen3.6-35b-a3b';
$model_name = getenv('VALMONT_LLM_MODEL_NAME') ?: 'Qwen 3.6 35B A3B';

// 1. Options globales AI Engine ----------------------------------------------
$opts = get_option('mwai_options', array());
if (!is_array($opts)) { $opts = array(); }

// Environnement LLM : type "custom" = compatible OpenAI. Les champs reels
// utilises par AI Engine sont 'endpoint' (pas 'url') et 'models'.
$opts['ai_envs'] = array(
  array(
    'name'     => 'LLM local (OpenAI-compatible)',
    'type'     => 'custom',
    'endpoint' => $base_url,
    'apikey'   => $api_key,
    'models'   => array(array('model' => $model, 'name' => $model_name)),
    'id'       => 'llm-local',
  ),
);
$opts['ai_default_env']   = 'llm-local';
$opts['ai_default_model'] = $model;

// Modules demonstres par la serie de notebooks
$opts['module_chatbots']   = true;
$opts['module_embeddings'] = true;
$opts['module_mcp']        = true;
$opts['module_forms']      = true;
$opts['module_workspace']  = true;
$opts['module_statistics'] = true;

// API publique REST (les endpoints mwai/v1 répondent aux clients)
$opts['public_api'] = true;

update_option('mwai_options', $opts);

// 2. Chatbot « valmont » -----------------------------------------------------
// mwai_chatbots est une LISTE de configurations completes (pas un dict par
// botId). On pousse une config complete, fidèle a celle produite par
// l'interface admin.
$chatbots = get_option('mwai_chatbots', array());
if (!is_array($chatbots)) { $chatbots = array(); }
$chatbots[] = array(
  'aiName'               => 'Valmont: ',
  'userName'             => 'Vous: ',
  'guestName'            => 'Visiteur: ',
  'textSend'             => 'Envoyer',
  'textClear'            => 'Effacer',
  'textInputPlaceholder' => 'Posez votre question a la maison...',
  'textInputMaxLength'   => 512,
  'startSentence'        => 'Bonjour, bienvenue a la Maison Valmont. Comment puis-je vous renseigner ?',
  'themeId'              => 'chatgpt',
  'window'               => false,
  'icon'                 => '',
  'iconText'             => '',
  'iconPosition'         => 'bottom-right',
  'botId'                => 'valmont',
  'instructions'         => "IMPORTANT: repondez en francais en texte brut. INTERDIT: emoji, symbole unicode, gras, italique, titre, liste a puces, tableau, markdown. Seulement des phrases simples separees par des retours a la ligne.",
  'scope'                => 'chatbot',
  'mode'                 => 'chat',
  'contentAware'         => false,
  'embeddingsEnvId'      => '',
  'model'                => $model,
  'temperature'          => 0.6,
  'maxMessages'          => 15,
  'maxTokens'            => 1024,
  'maxResults'           => 1,
  'functions'            => array(),
  'mcpServers'           => array(),
  'name'                 => 'Valmont',
  'fileUpload'           => false,
  'maxUploads'           => 1,
  'fileUploads'          => 0,
  'imageUpload'          => false,
);
update_option('mwai_chatbots', $chatbots);

// 3. mu-plugin : application passwords sans HTTPS (WordPress 6.8) ------------
$mu_dir  = '/var/www/html/wp-content/mu-plugins';
$mu_file = $mu_dir . '/force-app-passwords.php';
if (!is_dir($mu_dir)) { mkdir($mu_dir, 0755, true); }
if (!file_exists($mu_file)) {
  file_put_contents($mu_file, "<?php add_filter( 'wp_is_application_passwords_available', '__return_true' );" . PHP_EOL);
}

echo "OK: env 'llm-local' branché sur " . $base_url . PHP_EOL;
echo "OK: default_env=" . $opts['ai_default_env'] . ", default_model=" . $opts['ai_default_model'] . PHP_EOL;
echo "OK: chatbot 'valmont' (" . count($chatbots) . " chatbot(s) au total)" . PHP_EOL;
echo "OK: mu-plugin application passwords en place" . PHP_EOL;
echo "SUIVANT: creer un application password (cf. README, etape 5)." . PHP_EOL;
