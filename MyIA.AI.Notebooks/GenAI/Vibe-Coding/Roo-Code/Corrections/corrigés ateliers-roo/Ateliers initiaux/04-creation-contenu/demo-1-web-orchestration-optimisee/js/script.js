/**
 * TechPro Solutions - Script Principal
 * Interactivité moderne pour site web professionnel
 */

// =====================================
// CONFIGURATION GLOBALE
// =====================================

const config = {
  scrollOffset: 80,
  animationDelay: 100,
  smoothScrollDuration: 800
};

// =====================================
// NAVIGATION MOBILE & HAMBURGER MENU
// =====================================

class MobileNavigation {
  constructor() {
    this.nav = document.querySelector('.navbar');
    this.navToggle = document.querySelector('.navbar-toggle');
    this.navMenu = document.querySelector('.navbar-menu');
    this.navLinks = document.querySelectorAll('.navbar-menu a');
    this.body = document.body;
    
    this.init();
  }

  init() {
    if (this.navToggle) {
      this.navToggle.addEventListener('click', () => this.toggleMenu());
    }

    // Fermer le menu en cliquant sur un lien
    this.navLinks.forEach(link => {
      link.addEventListener('click', () => this.closeMenu());
    });

    // Fermer le menu en cliquant à l'extérieur
    document.addEventListener('click', (e) => {
      if (!this.nav.contains(e.target)) {
        this.closeMenu();
      }
    });

    // Gestion responsive automatique
    window.addEventListener('resize', () => this.handleResize());
  }

  toggleMenu() {
    const isOpen = this.navMenu.classList.contains('active');
    if (isOpen) {
      this.closeMenu();
    } else {
      this.openMenu();
    }
  }

  openMenu() {
    this.navMenu.classList.add('active');
    this.navToggle.classList.add('active');
    this.navToggle.setAttribute('aria-expanded', 'true');
    this.body.classList.add('nav-open');
  }

  closeMenu() {
    this.navMenu.classList.remove('active');
    this.navToggle.classList.remove('active');
    this.navToggle.setAttribute('aria-expanded', 'false');
    this.body.classList.remove('nav-open');
  }

  handleResize() {
    if (window.innerWidth > 768) {
      this.closeMenu();
    }
  }
}

// =====================================
// SMOOTH SCROLLING
// =====================================

class SmoothScrolling {
  constructor() {
    this.init();
  }

  init() {
    // Tous les liens d'ancrage
    const anchorLinks = document.querySelectorAll('a[href^="#"]');
    
    anchorLinks.forEach(link => {
      link.addEventListener('click', (e) => this.handleClick(e));
    });
  }

  handleClick(e) {
    e.preventDefault();
    const targetId = e.currentTarget.getAttribute('href');
    const targetElement = document.querySelector(targetId);

    if (targetElement) {
      const targetPosition = targetElement.offsetTop - config.scrollOffset;
      
      window.scrollTo({
        top: targetPosition,
        behavior: 'smooth'
      });
    }
  }
}

// =====================================
// ANIMATIONS À LA SCROLL
// =====================================

class ScrollAnimations {
  constructor() {
    this.elements = [];
    this.init();
  }

  init() {
    // Sélectionner tous les éléments à animer
    const animatableElements = document.querySelectorAll(`
      .service-card,
      .tech-category,
      .value-item,
      .testimonial-card,
      .stats-card,
      .hero-content,
      .section-header
    `);

    animatableElements.forEach((element, index) => {
      this.elements.push({
        element,
        delay: index * config.animationDelay,
        animated: false
      });
    });

    // Observer d'intersection pour déclencher les animations
    this.observer = new IntersectionObserver(
      (entries) => this.handleIntersection(entries),
      {
        threshold: 0.1,
        rootMargin: '0px 0px -50px 0px'
      }
    );

    this.elements.forEach(item => {
      this.observer.observe(item.element);
    });
  }

  handleIntersection(entries) {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        const elementData = this.elements.find(item => 
          item.element === entry.target
        );
        
        if (elementData && !elementData.animated) {
          setTimeout(() => {
            entry.target.classList.add('animate-in');
            elementData.animated = true;
          }, elementData.delay);
        }
      }
    });
  }
}

// =====================================
// FORMULAIRE DE CONTACT
// =====================================

class ContactForm {
  constructor() {
    this.form = document.querySelector('.quick-contact-form');
    this.inputs = [];
    this.init();
  }

  init() {
    if (!this.form) return;

    // Récupérer tous les champs du formulaire
    this.inputs = this.form.querySelectorAll('input, select, textarea');
    
    // Validation en temps réel
    this.inputs.forEach(input => {
      // Pour les select, utiliser uniquement 'change' (pas blur pour éviter les conflits)
      if (input.tagName.toLowerCase() === 'select') {
        input.addEventListener('change', () => {
          // Pour les selects, supprimer directement l'erreur et marquer comme valide si une valeur est sélectionnée
          if (input.value && input.value !== '') {
            this.clearErrors(input);
            input.classList.add('valid');
          }
        });
      } else {
        // Pour les autres inputs, utiliser blur et input
        input.addEventListener('blur', () => this.validateField(input));
        input.addEventListener('input', () => this.clearErrors(input));
      }
    });

    // Soumission du formulaire
    this.form.addEventListener('submit', (e) => this.handleSubmit(e));
  }

  validateField(field) {
    const tagName = field.tagName.toLowerCase();
    const value = tagName === 'select' ? field.value : field.value.trim();
    const type = field.type;
    const required = field.hasAttribute('required');

    // Supprimer les erreurs existantes
    this.clearErrors(field);

    if (required && !value) {
      if (tagName === 'select') {
        this.showError(field, 'Sélectionnez un élément dans la liste.');
      } else {
        this.showError(field, 'Ce champ est requis');
      }
      return false;
    }

    if (type === 'email' && value) {
      const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
      if (!emailRegex.test(value)) {
        this.showError(field, 'Format email invalide');
        return false;
      }
    }

    // Marquer comme valide
    field.classList.add('valid');
    return true;
  }

  showError(field, message) {
    field.classList.add('error');
    field.classList.remove('valid');
    
    // Créer ou mettre à jour le message d'erreur
    let errorElement = field.nextElementSibling;
    if (!errorElement || !errorElement.classList.contains('error-message')) {
      errorElement = document.createElement('span');
      errorElement.classList.add('error-message');
      field.parentNode.insertBefore(errorElement, field.nextSibling);
    }
    errorElement.textContent = message;
  }

  clearErrors(field) {
    field.classList.remove('error');
    const errorElement = field.nextElementSibling;
    if (errorElement && errorElement.classList.contains('error-message')) {
      errorElement.remove();
    }
  }

  handleSubmit(e) {
    e.preventDefault();
    
    let isValid = true;
    
    // Valider tous les champs
    this.inputs.forEach(input => {
      if (!this.validateField(input)) {
        isValid = false;
      }
    });

    if (isValid) {
      this.submitForm();
    } else {
      // Faire défiler vers le premier champ d'erreur
      const firstError = this.form.querySelector('.error');
      if (firstError) {
        firstError.scrollIntoView({ behavior: 'smooth', block: 'center' });
        firstError.focus();
      }
    }
  }

  async submitForm() {
    const submitBtn = this.form.querySelector('button[type="submit"]');
    const originalText = submitBtn.textContent;
    
    // Indiquer le chargement
    submitBtn.textContent = 'Envoi en cours...';
    submitBtn.disabled = true;

    // Simuler l'envoi (à remplacer par une vraie API)
    try {
      await new Promise(resolve => setTimeout(resolve, 2000));
      
      // Succès
      this.showSuccessMessage();
      this.form.reset();
      this.inputs.forEach(input => {
        input.classList.remove('valid', 'error');
      });
      
    } catch (error) {
      console.error('Erreur lors de l\'envoi:', error);
      this.showErrorMessage();
    } finally {
      // Restaurer le bouton
      submitBtn.textContent = originalText;
      submitBtn.disabled = false;
    }
  }

  showSuccessMessage() {
    const message = document.createElement('div');
    message.classList.add('form-message', 'success');
    message.textContent = '✅ Message envoyé avec succès ! Nous vous recontactons sous 24h.';
    
    this.form.insertBefore(message, this.form.firstChild);
    
    // Supprimer le message après 5 secondes
    setTimeout(() => message.remove(), 5000);
  }

  showErrorMessage() {
    const message = document.createElement('div');
    message.classList.add('form-message', 'error');
    message.textContent = '❌ Erreur lors de l\'envoi. Veuillez réessayer.';
    
    this.form.insertBefore(message, this.form.firstChild);
    
    // Supprimer le message après 5 secondes
    setTimeout(() => message.remove(), 5000);
  }
}

// =====================================
// NAVIGATION STICKY
// =====================================

class StickyNavigation {
  constructor() {
    this.header = document.querySelector('header');
    this.lastScrollY = window.scrollY;
    this.init();
  }

  init() {
    if (!this.header) return;

    window.addEventListener('scroll', () => this.handleScroll(), { passive: true });
  }

  handleScroll() {
    const currentScrollY = window.scrollY;
    
    if (currentScrollY > 100) {
      this.header.classList.add('scrolled');
      
      // Masquer/Afficher selon direction de scroll
      if (currentScrollY > this.lastScrollY && currentScrollY > 300) {
        this.header.classList.add('hidden');
      } else {
        this.header.classList.remove('hidden');
      }
    } else {
      this.header.classList.remove('scrolled', 'hidden');
    }
    
    this.lastScrollY = currentScrollY;
  }
}

// =====================================
// EFFETS INTERACTIFS
// =====================================

class InteractiveEffects {
  constructor() {
    this.init();
  }

  init() {
    // Effet parallax léger sur le hero
    this.initParallaxEffect();
    
    // Animations des compteurs
    this.initCounterAnimations();
    
    // Effet de typing sur les titres
    this.initTypingEffect();
  }

  initParallaxEffect() {
    const heroSection = document.querySelector('.hero');
    if (!heroSection) return;

    window.addEventListener('scroll', () => {
      const scrolled = window.pageYOffset;
      const rate = scrolled * -0.5;
      heroSection.style.transform = `translateY(${rate}px)`;
    }, { passive: true });
  }

  initCounterAnimations() {
    const statsNumbers = document.querySelectorAll('.stat-number');
    const observer = new IntersectionObserver((entries) => {
      entries.forEach(entry => {
        if (entry.isIntersecting) {
          this.animateCounter(entry.target);
          observer.unobserve(entry.target);
        }
      });
    }, { threshold: 0.5 });

    statsNumbers.forEach(number => observer.observe(number));
  }

  animateCounter(element) {
    const target = parseInt(element.textContent);
    const duration = 2000;
    const steps = 60;
    const increment = target / steps;
    let current = 0;

    const timer = setInterval(() => {
      current += increment;
      if (current >= target) {
        current = target;
        clearInterval(timer);
      }
      element.textContent = Math.floor(current);
    }, duration / steps);
  }

  initTypingEffect() {
    const typingElements = document.querySelectorAll('[data-typing]');
    
    typingElements.forEach(element => {
      const text = element.textContent;
      element.textContent = '';
      element.style.borderRight = '2px solid var(--color-accent)';
      
      let i = 0;
      const typeWriter = () => {
        if (i < text.length) {
          element.textContent += text.charAt(i);
          i++;
          setTimeout(typeWriter, 100);
        } else {
          // Supprimer le curseur après la fin
          setTimeout(() => {
            element.style.borderRight = 'none';
          }, 1000);
        }
      };

      // Déclencher l'effet quand l'élément est visible
      const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
          if (entry.isIntersecting) {
            setTimeout(typeWriter, 500);
            observer.unobserve(entry.target);
          }
        });
      }, { threshold: 0.5 });

      observer.observe(element);
    });
  }
}

// =====================================
// INITIALISATION GLOBALE
// =====================================

class App {
  constructor() {
    this.init();
  }

  init() {
    // Attendre que le DOM soit chargé
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', () => this.initializeModules());
    } else {
      this.initializeModules();
    }
  }

  initializeModules() {
    console.log('🚀 TechPro Solutions - Initialisation des modules');
    
    try {
      // Initialiser tous les modules
      new MobileNavigation();
      new SmoothScrolling();
      new ScrollAnimations();
      new ContactForm();
      new StickyNavigation();
      new InteractiveEffects();
      
      console.log('✅ Tous les modules sont initialisés');
      
      // Ajouter la classe "loaded" au body pour déclencher les animations CSS
      document.body.classList.add('loaded');
      
    } catch (error) {
      console.error('❌ Erreur lors de l\'initialisation:', error);
    }
  }
}

// =====================================
// DÉMARRAGE DE L'APPLICATION
// =====================================

new App();

// Export pour les tests (si nécessaire)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    MobileNavigation,
    SmoothScrolling,
    ScrollAnimations,
    ContactForm,
    StickyNavigation,
    InteractiveEffects,
    App
  };
}