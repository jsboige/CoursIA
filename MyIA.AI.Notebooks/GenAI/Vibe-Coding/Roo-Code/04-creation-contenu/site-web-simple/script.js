/**
 * Script.js - Fonctionnalités JavaScript pour Le Petit Pain - Boulangerie Artisanale
 */

// Attendre que le DOM soit complètement chargé
document.addEventListener('DOMContentLoaded', () => {
    console.log('Site Le Petit Pain chargé !');
    
    // Initialiser toutes les fonctionnalités
    initNavigation();
    initContactForm();
    initScrollEffects();
    initBackToTop();
});

/**
 * Gestion de la navigation responsive
 */
function initNavigation() {
    const menuToggle = document.getElementById('menu-toggle');
    const menu = document.querySelector('.menu');
    const menuLinks = document.querySelectorAll('.menu a');
    const header = document.querySelector('header');
    
    // Toggle menu sur mobile
    if (menuToggle) {
        menuToggle.addEventListener('click', () => {
            menu.classList.toggle('active');
            menuToggle.setAttribute('aria-expanded', 
                menuToggle.getAttribute('aria-expanded') === 'true' ? 'false' : 'true'
            );
        });
    }
    
    // Fermer le menu après un clic sur un lien
    menuLinks.forEach(link => {
        link.addEventListener('click', () => {
            menu.classList.remove('active');
            if (menuToggle) {
                menuToggle.setAttribute('aria-expanded', 'false');
            }
        });
    });
    
    // Changer le style du header au scroll
    window.addEventListener('scroll', () => {
        if (window.scrollY > 100) {
            header.classList.add('scrolled');
        } else {
            header.classList.remove('scrolled');
        }
    });
}

/**
 * Validation et soumission du formulaire de contact
 */
function initContactForm() {
    const contactForm = document.getElementById('contactForm');
    
    if (contactForm) {
        contactForm.addEventListener('submit', (e) => {
            e.preventDefault();
            
            // Récupérer les valeurs du formulaire
            const name = document.getElementById('name').value.trim();
            const email = document.getElementById('email').value.trim();
            const subject = document.getElementById('subject').value.trim();
            const message = document.getElementById('message').value.trim();
            
            // Valider les champs
            if (!validateContactForm(name, email, subject, message)) {
                return;
            }
            
            // Simuler l'envoi du formulaire (dans un cas réel, vous utiliseriez AJAX ou Fetch)
            console.log('Formulaire soumis avec succès !');
            console.log({ name, email, subject, message });
            
            // Afficher un message de succès
            showFormMessage('Votre message a été envoyé avec succès ! Nous vous répondrons dans les plus brefs délais.', 'success');
            
            // Réinitialiser le formulaire
            contactForm.reset();
        });
    }
}

/**
 * Valide les champs du formulaire de contact
 */
function validateContactForm(name, email, subject, message) {
    // Réinitialiser les messages d'erreur précédents
    clearFormErrors();
    
    let isValid = true;
    
    // Valider le nom
    if (name === '') {
        showFieldError('name', 'Veuillez entrer votre nom');
        isValid = false;
    }
    
    // Valider l'email
    if (email === '') {
        showFieldError('email', 'Veuillez entrer votre adresse email');
        isValid = false;
    } else if (!isValidEmail(email)) {
        showFieldError('email', 'Veuillez entrer une adresse email valide');
        isValid = false;
    }
    
    // Valider le sujet
    if (subject === '') {
        showFieldError('subject', 'Veuillez entrer un sujet');
        isValid = false;
    }
    
    // Valider le message
    if (message === '') {
        showFieldError('message', 'Veuillez entrer votre message');
        isValid = false;
    } else if (message.length < 10) {
        showFieldError('message', 'Votre message doit contenir au moins 10 caractères');
        isValid = false;
    }
    
    return isValid;
}

/**
 * Vérifie si une adresse email est valide
 */
function isValidEmail(email) {
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    return emailRegex.test(email);
}

/**
 * Affiche une erreur pour un champ spécifique
 */
function showFieldError(fieldId, errorMessage) {
    const field = document.getElementById(fieldId);
    const errorElement = document.createElement('div');
    errorElement.className = 'error-message';
    errorElement.textContent = errorMessage;
    errorElement.style.color = 'var(--danger-color)';
    errorElement.style.fontSize = '0.8rem';
    errorElement.style.marginTop = '0.3rem';
    
    field.classList.add('error');
    field.parentNode.appendChild(errorElement);
}

/**
 * Supprime tous les messages d'erreur du formulaire
 */
function clearFormErrors() {
    const errorMessages = document.querySelectorAll('.error-message');
    const errorFields = document.querySelectorAll('.error');
    
    errorMessages.forEach(error => error.remove());
    errorFields.forEach(field => field.classList.remove('error'));
}

/**
 * Affiche un message de succès ou d'erreur pour le formulaire
 */
function showFormMessage(message, type) {
    const contactForm = document.getElementById('contactForm');
    const formMessage = document.createElement('div');
    formMessage.className = `form-message ${type}`;
    formMessage.textContent = message;
    
    // Styles pour le message
    formMessage.style.padding = '1rem';
    formMessage.style.marginTop = '1rem';
    formMessage.style.borderRadius = 'var(--border-radius)';
    
    if (type === 'success') {
        formMessage.style.backgroundColor = 'rgba(39, 174, 96, 0.1)';
        formMessage.style.color = 'var(--success-color)';
        formMessage.style.border = '1px solid var(--success-color)';
    } else {
        formMessage.style.backgroundColor = 'rgba(231, 76, 60, 0.1)';
        formMessage.style.color = 'var(--danger-color)';
        formMessage.style.border = '1px solid var(--danger-color)';
    }
    
    // Supprimer les messages précédents
    const oldMessages = document.querySelectorAll('.form-message');
    oldMessages.forEach(msg => msg.remove());
    
    // Ajouter le nouveau message
    contactForm.parentNode.insertBefore(formMessage, contactForm.nextSibling);
    
    // Faire défiler jusqu'au message
    formMessage.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    
    // Supprimer le message après 5 secondes si c'est un succès
    if (type === 'success') {
        setTimeout(() => {
            formMessage.style.opacity = '0';
            setTimeout(() => formMessage.remove(), 300);
        }, 5000);
    }
}

/**
 * Effets de défilement et animations
 */
function initScrollEffects() {
    // Animation des éléments au scroll
    const animateElements = document.querySelectorAll('.product-card, .value-card, .info-item');
    
    // Ajouter des classes pour l'animation initiale
    animateElements.forEach(element => {
        element.style.opacity = '0';
        element.style.transform = 'translateY(20px)';
        element.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
    });
    
    // Observer les éléments et les animer lorsqu'ils sont visibles
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
                observer.unobserve(entry.target);
            }
        });
    }, { threshold: 0.1 });
    
    animateElements.forEach(element => {
        observer.observe(element);
    });
}

/**
 * Bouton de retour en haut de page
 */
function initBackToTop() {
    const backToTopButton = document.getElementById('backToTop');
    
    if (backToTopButton) {
        // Afficher/masquer le bouton en fonction du défilement
        window.addEventListener('scroll', () => {
            if (window.scrollY > 500) {
                backToTopButton.classList.add('visible');
            } else {
                backToTopButton.classList.remove('visible');
            }
        });
        
        // Action du bouton
        backToTopButton.addEventListener('click', (e) => {
            e.preventDefault();
            window.scrollTo({
                top: 0,
                behavior: 'smooth'
            });
        });
    }
}

/**
 * Fonction utilitaire pour animer les défilements vers les ancres
 */
document.querySelectorAll('a[href^="#"]').forEach(anchor => {
    anchor.addEventListener('click', function(e) {
        e.preventDefault();
        
        const targetId = this.getAttribute('href');
        if (targetId === '#') return;
        
        const targetElement = document.querySelector(targetId);
        if (targetElement) {
            const headerHeight = document.querySelector('header').offsetHeight;
            const targetPosition = targetElement.getBoundingClientRect().top + window.scrollY - headerHeight;
            
            window.scrollTo({
                top: targetPosition,
                behavior: 'smooth'
            });
        }
    });
});