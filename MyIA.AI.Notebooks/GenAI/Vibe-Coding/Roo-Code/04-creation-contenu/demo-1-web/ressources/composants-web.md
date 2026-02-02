# Composants web et modèles de pages

Ce document présente différents composants HTML/CSS et modèles de pages que vous pouvez utiliser comme base pour votre site web.

## Composants de navigation

### Barre de navigation responsive

```html
<!-- HTML -->
<nav class="navbar">
  <div class="navbar-logo">
    <a href="index.html">Nom du Site</a>
  </div>
  <button class="navbar-toggle" aria-label="Menu">
    <span class="navbar-toggle-icon"></span>
  </button>
  <ul class="navbar-menu">
    <li><a href="index.html" class="active">Accueil</a></li>
    <li><a href="about.html">À propos</a></li>
    <li><a href="services.html">Services</a></li>
    <li><a href="contact.html">Contact</a></li>
  </ul>
</nav>
```

```css
/* CSS */
.navbar {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 1rem 2rem;
  background-color: #ffffff;
  box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
}

.navbar-logo a {
  font-size: 1.5rem;
  font-weight: bold;
  text-decoration: none;
  color: #333;
}

.navbar-menu {
  display: flex;
  list-style: none;
  margin: 0;
  padding: 0;
}

.navbar-menu li {
  margin-left: 1.5rem;
}

.navbar-menu a {
  text-decoration: none;
  color: #555;
  font-weight: 500;
  transition: color 0.3s;
}

.navbar-menu a:hover, .navbar-menu a.active {
  color: #0066cc;
}

.navbar-toggle {
  display: none;
  background: none;
  border: none;
  cursor: pointer;
}

@media (max-width: 768px) {
  .navbar-toggle {
    display: block;
  }
  
  .navbar-menu {
    position: absolute;
    top: 60px;
    left: 0;
    right: 0;
    flex-direction: column;
    background-color: #ffffff;
    box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
    display: none;
    padding: 1rem 0;
  }
  
  .navbar-menu.active {
    display: flex;
  }
  
  .navbar-menu li {
    margin: 0;
    text-align: center;
    padding: 0.5rem 0;
  }
}
```

```javascript
// JavaScript pour la navigation responsive
document.querySelector('.navbar-toggle').addEventListener('click', function() {
  document.querySelector('.navbar-menu').classList.toggle('active');
});
```

### Fil d'Ariane (Breadcrumb)

```html
<!-- HTML -->
<nav aria-label="Fil d'Ariane" class="breadcrumb">
  <ol>
    <li><a href="index.html">Accueil</a></li>
    <li><a href="services.html">Services</a></li>
    <li aria-current="page">Développement Web</li>
  </ol>
</nav>
```

```css
/* CSS */
.breadcrumb {
  padding: 0.75rem 1rem;
  background-color: #f8f9fa;
  border-radius: 0.25rem;
  margin-bottom: 1rem;
}

.breadcrumb ol {
  display: flex;
  flex-wrap: wrap;
  list-style: none;
  margin: 0;
  padding: 0;
}

.breadcrumb li + li::before {
  content: "/";
  padding: 0 0.5rem;
  color: #6c757d;
}

.breadcrumb a {
  text-decoration: none;
  color: #0066cc;
}

.breadcrumb li:last-child {
  color: #6c757d;
}
```

## Composants de mise en page

### Section Hero

```html
<!-- HTML -->
<section class="hero">
  <div class="hero-content">
    <h1>Titre principal captivant</h1>
    <p>Une description concise et engageante de votre entreprise ou service.</p>
    <div class="hero-buttons">
      <a href="#" class="btn btn-primary">Appel à l'action</a>
      <a href="#" class="btn btn-secondary">En savoir plus</a>
    </div>
  </div>
</section>
```

```css
/* CSS */
.hero {
  position: relative;
  height: 80vh;
  min-height: 500px;
  display: flex;
  align-items: center;
  justify-content: center;
  background-image: linear-gradient(rgba(0, 0, 0, 0.5), rgba(0, 0, 0, 0.5)), url('images/hero-bg.jpg');
  background-size: cover;
  background-position: center;
  color: white;
  text-align: center;
}

.hero-content {
  max-width: 800px;
  padding: 0 2rem;
}

.hero h1 {
  font-size: 3rem;
  margin-bottom: 1rem;
}

.hero p {
  font-size: 1.25rem;
  margin-bottom: 2rem;
}

.hero-buttons {
  display: flex;
  justify-content: center;
  gap: 1rem;
}

.btn {
  display: inline-block;
  padding: 0.75rem 1.5rem;
  border-radius: 0.25rem;
  text-decoration: none;
  font-weight: bold;
  transition: background-color 0.3s, transform 0.2s;
}

.btn:hover {
  transform: translateY(-2px);
}

.btn-primary {
  background-color: #0066cc;
  color: white;
}

.btn-primary:hover {
  background-color: #0055aa;
}

.btn-secondary {
  background-color: transparent;
  color: white;
  border: 2px solid white;
}

.btn-secondary:hover {
  background-color: rgba(255, 255, 255, 0.1);
}

@media (max-width: 768px) {
  .hero h1 {
    font-size: 2rem;
  }
  
  .hero p {
    font-size: 1rem;
  }
  
  .hero-buttons {
    flex-direction: column;
    align-items: center;
  }
}
```

### Grille de cartes

```html
<!-- HTML -->
<section class="card-grid">
  <div class="card">
    <img src="images/card1.jpg" alt="Description de l'image">
    <div class="card-content">
      <h3>Titre de la carte</h3>
      <p>Description courte du contenu de cette carte.</p>
      <a href="#" class="card-link">En savoir plus</a>
    </div>
  </div>
  
  <div class="card">
    <img src="images/card2.jpg" alt="Description de l'image">
    <div class="card-content">
      <h3>Titre de la carte</h3>
      <p>Description courte du contenu de cette carte.</p>
      <a href="#" class="card-link">En savoir plus</a>
    </div>
  </div>
  
  <div class="card">
    <img src="images/card3.jpg" alt="Description de l'image">
    <div class="card-content">
      <h3>Titre de la carte</h3>
      <p>Description courte du contenu de cette carte.</p>
      <a href="#" class="card-link">En savoir plus</a>
    </div>
  </div>
</section>
```

```css
/* CSS */
.card-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
  gap: 2rem;
  padding: 2rem;
}

.card {
  border-radius: 0.5rem;
  overflow: hidden;
  box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);
  transition: transform 0.3s, box-shadow 0.3s;
}

.card:hover {
  transform: translateY(-5px);
  box-shadow: 0 10px 20px rgba(0, 0, 0, 0.1);
}

.card img {
  width: 100%;
  height: 200px;
  object-fit: cover;
}

.card-content {
  padding: 1.5rem;
}

.card h3 {
  margin-top: 0;
  margin-bottom: 0.75rem;
  font-size: 1.25rem;
}

.card p {
  color: #666;
  margin-bottom: 1.5rem;
}

.card-link {
  display: inline-block;
  color: #0066cc;
  text-decoration: none;
  font-weight: 500;
  position: relative;
}

.card-link::after {
  content: '';
  position: absolute;
  bottom: -2px;
  left: 0;
  width: 0;
  height: 2px;
  background-color: #0066cc;
  transition: width 0.3s;
}

.card-link:hover::after {
  width: 100%;
}
```

## Composants de formulaire

### Formulaire de contact

```html
<!-- HTML -->
<form class="contact-form">
  <div class="form-group">
    <label for="name">Nom</label>
    <input type="text" id="name" name="name" required>
  </div>
  
  <div class="form-group">
    <label for="email">Email</label>
    <input type="email" id="email" name="email" required>
  </div>
  
  <div class="form-group">
    <label for="subject">Sujet</label>
    <select id="subject" name="subject">
      <option value="general">Renseignement général</option>
      <option value="support">Support technique</option>
      <option value="business">Opportunité commerciale</option>
    </select>
  </div>
  
  <div class="form-group">
    <label for="message">Message</label>
    <textarea id="message" name="message" rows="5" required></textarea>
  </div>
  
  <div class="form-group form-checkbox">
    <input type="checkbox" id="consent" name="consent" required>
    <label for="consent">J'accepte que mes données soient traitées conformément à la politique de confidentialité.</label>
  </div>
  
  <button type="submit" class="btn btn-primary">Envoyer</button>
</form>
```

```css
/* CSS */
.contact-form {
  max-width: 600px;
  margin: 0 auto;
  padding: 2rem;
  background-color: #f9f9f9;
  border-radius: 0.5rem;
}

.form-group {
  margin-bottom: 1.5rem;
}

.form-group label {
  display: block;
  margin-bottom: 0.5rem;
  font-weight: 500;
}

.form-group input,
.form-group select,
.form-group textarea {
  width: 100%;
  padding: 0.75rem;
  border: 1px solid #ddd;
  border-radius: 0.25rem;
  font-size: 1rem;
  transition: border-color 0.3s;
}

.form-group input:focus,
.form-group select:focus,
.form-group textarea:focus {
  border-color: #0066cc;
  outline: none;
}

.form-checkbox {
  display: flex;
  align-items: flex-start;
}

.form-checkbox input {
  width: auto;
  margin-top: 0.25rem;
  margin-right: 0.75rem;
}

.form-checkbox label {
  margin-bottom: 0;
  font-weight: normal;
  font-size: 0.9rem;
}

.contact-form .btn {
  padding: 0.75rem 2rem;
  background-color: #0066cc;
  color: white;
  border: none;
  border-radius: 0.25rem;
  font-size: 1rem;
  cursor: pointer;
  transition: background-color 0.3s;
}

.contact-form .btn:hover {
  background-color: #0055aa;
}
```

## Modèles de pages complètes

### Page d'accueil

```html
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Nom de l'entreprise - Accueil</title>
    <link rel="stylesheet" href="css/style.css">
</head>
<body>
    <header>
        <nav class="navbar">
            <div class="navbar-logo">
                <a href="index.html">Nom de l'entreprise</a>
            </div>
            <button class="navbar-toggle" aria-label="Menu">
                <span class="navbar-toggle-icon"></span>
            </button>
            <ul class="navbar-menu">
                <li><a href="index.html" class="active">Accueil</a></li>
                <li><a href="services.html">Services</a></li>
                <li><a href="about.html">À propos</a></li>
                <li><a href="contact.html">Contact</a></li>
            </ul>
        </nav>
    </header>

    <main>
        <section class="hero">
            <div class="hero-content">
                <h1>Titre principal captivant</h1>
                <p>Une description concise et engageante de votre entreprise ou service.</p>
                <div class="hero-buttons">
                    <a href="#" class="btn btn-primary">Appel à l'action</a>
                    <a href="#" class="btn btn-secondary">En savoir plus</a>
                </div>
            </div>
        </section>

        <section class="features">
            <div class="container">
                <h2 class="section-title">Nos services</h2>
                <div class="card-grid">
                    <div class="card">
                        <img src="images/service1.jpg" alt="Service 1">
                        <div class="card-content">
                            <h3>Service 1</h3>
                            <p>Description du service et de ses avantages.</p>
                            <a href="#" class="card-link">En savoir plus</a>
                        </div>
                    </div>
                    
                    <div class="card">
                        <img src="images/service2.jpg" alt="Service 2">
                        <div class="card-content">
                            <h3>Service 2</h3>
                            <p>Description du service et de ses avantages.</p>
                            <a href="#" class="card-link">En savoir plus</a>
                        </div>
                    </div>
                    
                    <div class="card">
                        <img src="images/service3.jpg" alt="Service 3">
                        <div class="card-content">
                            <h3>Service 3</h3>
                            <p>Description du service et de ses avantages.</p>
                            <a href="#" class="card-link">En savoir plus</a>
                        </div>
                    </div>
                </div>
            </div>
        </section>

        <section class="about-preview">
            <div class="container">
                <div class="about-content">
                    <div class="about-text">
                        <h2>À propos de nous</h2>
                        <p>Présentation concise de votre entreprise, son histoire et sa mission.</p>
                        <p>Valeurs et engagements qui vous distinguent de la concurrence.</p>
                        <a href="about.html" class="btn btn-primary">En savoir plus</a>
                    </div>
                    <div class="about-image">
                        <img src="images/about.jpg" alt="À propos de nous">
                    </div>
                </div>
            </div>
        </section>

        <section class="cta">
            <div class="container">
                <h2>Prêt à commencer?</h2>
                <p>Contactez-nous dès aujourd'hui pour discuter de votre projet.</p>
                <a href="contact.html" class="btn btn-primary">Nous contacter</a>
            </div>
        </section>
    </main>

    <footer>
        <div class="container">
            <div class="footer-content">
                <div class="footer-logo">
                    <h3>Nom de l'entreprise</h3>
                    <p>Slogan ou phrase d'accroche</p>
                </div>
                <div class="footer-links">
                    <h4>Liens rapides</h4>
                    <ul>
                        <li><a href="index.html">Accueil</a></li>
                        <li><a href="services.html">Services</a></li>
                        <li><a href="about.html">À propos</a></li>
                        <li><a href="contact.html">Contact</a></li>
                    </ul>
                </div>
                <div class="footer-contact">
                    <h4>Contact</h4>
                    <p>Adresse, Ville, Code postal</p>
                    <p>Email: contact@example.com</p>
                    <p>Téléphone: 01 23 45 67 89</p>
                </div>
            </div>
            <div class="footer-bottom">
                <p>&copy; 2025 Nom de l'entreprise. Tous droits réservés.</p>
            </div>
        </div>
    </footer>

    <script src="js/main.js"></script>
</body>
</html>
```

### Page de contact

```html
<!DOCTYPE html>
<html lang="fr">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Contact - Nom de l'entreprise</title>
    <link rel="stylesheet" href="css/style.css">
</head>
<body>
    <header>
        <!-- Navigation (même que page d'accueil) -->
    </header>

    <main>
        <section class="page-header">
            <div class="container">
                <h1>Contactez-nous</h1>
                <nav aria-label="Fil d'Ariane" class="breadcrumb">
                    <ol>
                        <li><a href="index.html">Accueil</a></li>
                        <li aria-current="page">Contact</li>
                    </ol>
                </nav>
            </div>
        </section>

        <section class="contact-section">
            <div class="container">
                <div class="contact-grid">
                    <div class="contact-info">
                        <h2>Nos coordonnées</h2>
                        <div class="info-item">
                            <h3>Adresse</h3>
                            <p>123 Rue Exemple<br>75000 Paris<br>France</p>
                        </div>
                        <div class="info-item">
                            <h3>Téléphone</h3>
                            <p>01 23 45 67 89</p>
                        </div>
                        <div class="info-item">
                            <h3>Email</h3>
                            <p>contact@example.com</p>
                        </div>
                        <div class="info-item">
                            <h3>Horaires</h3>
                            <p>Lundi - Vendredi: 9h - 18h<br>Samedi: 10h - 16h<br>Dimanche: Fermé</p>
                        </div>
                    </div>
                    <div class="contact-form-container">
                        <h2>Envoyez-nous un message</h2>
                        <form class="contact-form">
                            <div class="form-group">
                                <label for="name">Nom</label>
                                <input type="text" id="name" name="name" required>
                            </div>
                            
                            <div class="form-group">
                                <label for="email">Email</label>
                                <input type="email" id="email" name="email" required>
                            </div>
                            
                            <div class="form-group">
                                <label for="subject">Sujet</label>
                                <select id="subject" name="subject">
                                    <option value="general">Renseignement général</option>
                                    <option value="support">Support technique</option>
                                    <option value="business">Opportunité commerciale</option>
                                </select>
                            </div>
                            
                            <div class="form-group">
                                <label for="message">Message</label>
                                <textarea id="message" name="message" rows="5" required></textarea>
                            </div>
                            
                            <div class="form-group form-checkbox">
                                <input type="checkbox" id="consent" name="consent" required>
                                <label for="consent">J'accepte que mes données soient traitées conformément à la politique de confidentialité.</label>
                            </div>
                            
                            <button type="submit" class="btn btn-primary">Envoyer</button>
                        </form>
                    </div>
                </div>
            </div>
        </section>

        <section class="map-section">
            <div class="container">
                <h2>Nous trouver</h2>
                <div class="map-container">
                    <!-- Intégrer ici une carte Google Maps ou OpenStreetMap -->
                    <iframe src="https://www.openstreetmap.org/export/embed.html?bbox=2.3%2C48.8%2C2.4%2C48.9&amp;layer=mapnik" width="100%" height="400" frameborder="0" style="border: 1px solid #ccc"></iframe>
                </div>
            </div>
        </section>
    </main>

    <footer>
        <!-- Pied de page (même que page d'accueil) -->
    </footer>

    <script src="js/main.js"></script>
</body>
</html>
```

## Conseils pour un site web efficace

### Bonnes pratiques HTML

1. **Structure sémantique**
   - Utilisez les balises HTML5 appropriées (`<header>`, `<nav>`, `<main>`, `<section>`, `<article>`, `<footer>`, etc.)
   - Structurez correctement les titres (`<h1>` à `<h6>`) de manière hiérarchique
   - Utilisez des attributs `alt` descriptifs pour les images

2. **Accessibilité**
   - Assurez un contraste suffisant entre le texte et l'arrière-plan
   - Incluez des attributs ARIA lorsque nécessaire
   - Rendez tous les éléments interactifs accessibles au clavier
   - Structurez les formulaires avec des labels associés aux champs

3. **Performance**
   - Optimisez les images (taille et format appropriés)
   - Minimisez le nombre de requêtes HTTP
   - Placez les scripts JavaScript en fin de document
   - Utilisez le chargement différé pour les ressources non critiques

### Conseils CSS

1. **Organisation**
   - Utilisez une approche modulaire (comme BEM ou SMACSS)
   - Regroupez les styles par composant
   - Commentez les sections importantes

2. **Responsive design**
   - Adoptez une approche "mobile-first"
   - Utilisez des unités relatives (rem, em, %) plutôt que des pixels
   - Testez sur différentes tailles d'écran
   - Utilisez les media queries pour adapter le design

3. **Optimisation**
   - Évitez les sélecteurs trop complexes
   - Limitez l'utilisation des animations
   - Préférez Flexbox et Grid aux positionnements absolus

### Conseils JavaScript

1. **Bonnes pratiques**
   - Utilisez JavaScript pour améliorer l'expérience, pas pour la rendre essentielle
   - Validez les formulaires côté client ET côté serveur
   - Gérez correctement les erreurs

2. **Performance**
   - Évitez la manipulation excessive du DOM
   - Utilisez la délégation d'événements
   - Minimisez et compressez les fichiers JavaScript

3. **Compatibilité**
   - Testez sur différents navigateurs
   - Utilisez des polyfills si nécessaire
   - Considérez l'utilisation de frameworks modernes pour les projets complexes