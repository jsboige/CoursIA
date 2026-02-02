/**
 * DigitalBoost - Page de Contact
 * JavaScript pour la gestion du formulaire de contact
 */

// ===== VARIABLES GLOBALES =====
let formSubmitted = false;

// ===== INITIALISATION =====
document.addEventListener('DOMContentLoaded', function() {
    initContactForm();
    initFormValidation();
});

// ===== GESTION DU FORMULAIRE DE CONTACT =====
function initContactForm() {
    const form = document.getElementById('contact-form');
    const successMessage = document.getElementById('form-success');
    
    if (!form || !successMessage) return;

    form.addEventListener('submit', function(e) {
        e.preventDefault();
        
        if (formSubmitted) return;
        
        // Validation complète du formulaire
        if (validateForm(form)) {
            submitForm(form, successMessage);
        }
    });
}

// ===== VALIDATION DU FORMULAIRE =====
function initFormValidation() {
    const form = document.getElementById('contact-form');
    if (!form) return;

    // Validation en temps réel
    const inputs = form.querySelectorAll('input, textarea, select');
    inputs.forEach(input => {
        // Validation au blur (perte de focus)
        input.addEventListener('blur', function() {
            validateField(this);
        });

        // Validation lors de la saisie pour les champs obligatoires
        input.addEventListener('input', function() {
            if (this.hasAttribute('required')) {
                clearError(this);
            }
        });
    });

    // Validation spéciale pour l'email
    const emailInput = document.getElementById('email');
    if (emailInput) {
        emailInput.addEventListener('input', function() {
            if (this.value && !isValidEmail(this.value)) {
                showError(this, 'Veuillez saisir une adresse email valide');
            } else {
                clearError(this);
            }
        });
    }

    // Validation spéciale pour le téléphone
    const phoneInput = document.getElementById('phone');
    if (phoneInput) {
        phoneInput.addEventListener('input', function() {
            if (this.value && !isValidPhone(this.value)) {
                showError(this, 'Veuillez saisir un numéro de téléphone valide');
            } else {
                clearError(this);
            }
        });
    }
}

function validateForm(form) {
    let isValid = true;
    const requiredFields = form.querySelectorAll('[required]');
    
    requiredFields.forEach(field => {
        if (!validateField(field)) {
            isValid = false;
        }
    });
    
    return isValid;
}

function validateField(field) {
    const value = field.value.trim();
    let isValid = true;
    let errorMessage = '';
    
    // Validation des champs obligatoires
    if (field.hasAttribute('required') && !value) {
        errorMessage = 'Ce champ est obligatoire';
        isValid = false;
    }
    // Validation spécifique par type de champ
    else if (value) {
        switch (field.type) {
            case 'email':
                if (!isValidEmail(value)) {
                    errorMessage = 'Veuillez saisir une adresse email valide';
                    isValid = false;
                }
                break;
            case 'tel':
                if (!isValidPhone(value)) {
                    errorMessage = 'Veuillez saisir un numéro de téléphone valide';
                    isValid = false;
                }
                break;
        }
        
        // Validation pour les champs de texte (nom, prénom)
        if (field.id === 'firstName' || field.id === 'lastName') {
            if (value.length < 2) {
                errorMessage = 'Ce champ doit contenir au moins 2 caractères';
                isValid = false;
            } else if (!/^[a-zA-ZÀ-ÿ\s-']+$/.test(value)) {
                errorMessage = 'Ce champ ne peut contenir que des lettres';
                isValid = false;
            }
        }
        
        // Validation pour le message
        if (field.id === 'message' && value.length < 10) {
            errorMessage = 'Votre message doit contenir au moins 10 caractères';
            isValid = false;
        }
        
        // Validation pour les select
        if (field.tagName === 'SELECT' && field.hasAttribute('required') && !value) {
            errorMessage = 'Veuillez faire un choix';
            isValid = false;
        }
        
        // Validation pour les checkbox obligatoires
        if (field.type === 'checkbox' && field.hasAttribute('required') && !field.checked) {
            errorMessage = 'Vous devez accepter cette condition';
            isValid = false;
        }
    }
    
    if (!isValid) {
        showError(field, errorMessage);
        return false;
    } else {
        clearError(field);
        return true;
    }
}

function showError(field, message) {
    const errorElement = document.getElementById(field.name + '-error');
    if (errorElement) {
        errorElement.textContent = message;
        errorElement.style.display = 'block';
    }
    
    field.classList.add('error');
    field.setAttribute('aria-invalid', 'true');
}

function clearError(field) {
    const errorElement = document.getElementById(field.name + '-error');
    if (errorElement) {
        errorElement.textContent = '';
        errorElement.style.display = 'none';
    }
    
    field.classList.remove('error');
    field.removeAttribute('aria-invalid');
}

// ===== FONCTIONS DE VALIDATION =====
function isValidEmail(email) {
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    return emailRegex.test(email);
}

function isValidPhone(phone) {
    // Regex pour numéros français et internationaux
    const phoneRegex = /^(?:(?:\+|00)33|0)\s*[1-9](?:[\s.-]*\d{2}){4}$/;
    return phoneRegex.test(phone.replace(/\s/g, ''));
}

// ===== SOUMISSION DU FORMULAIRE =====
function submitForm(form, successMessage) {
    const submitButton = form.querySelector('button[type="submit"]');
    const buttonText = submitButton.querySelector('.btn-text');
    const buttonLoader = submitButton.querySelector('.btn-loader');
    
    // Afficher le loader
    formSubmitted = true;
    submitButton.disabled = true;
    buttonText.style.display = 'none';
    buttonLoader.style.display = 'inline-flex';
    
    // Collecter les données du formulaire
    const formData = new FormData(form);
    const data = Object.fromEntries(formData.entries());
    
    // Simulation d'envoi (remplacer par un vrai appel API)
    setTimeout(() => {
        // Simuler un succès (remplacer par une vraie gestion d'erreur)
        if (Math.random() > 0.1) { // 90% de chance de succès
            showSuccessMessage(form, successMessage);
            
            // Réinitialiser le formulaire
            form.reset();
            
            // Analytics - tracker l'événement de contact
            if (typeof gtag !== 'undefined') {
                gtag('event', 'contact_form_submit', {
                    event_category: 'Contact',
                    event_label: data.subject || 'Unknown'
                });
            }
        } else {
            showErrorMessage(form);
        }
        
        // Réinitialiser le bouton
        resetSubmitButton(submitButton, buttonText, buttonLoader);
        
    }, 2000); // Simulation d'une requête de 2 secondes
}

function showSuccessMessage(form, successMessage) {
    // Masquer le formulaire avec animation
    form.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
    form.style.opacity = '0';
    form.style.transform = 'translateY(-20px)';
    
    setTimeout(() => {
        form.style.display = 'none';
        successMessage.style.display = 'block';
        successMessage.style.opacity = '0';
        successMessage.style.transform = 'translateY(20px)';
        
        // Animation d'apparition du message de succès
        setTimeout(() => {
            successMessage.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
            successMessage.style.opacity = '1';
            successMessage.style.transform = 'translateY(0)';
        }, 50);
        
        // Scroll vers le message de succès
        successMessage.scrollIntoView({ behavior: 'smooth', block: 'center' });
        
        // Focus sur le message de succès pour l'accessibilité
        successMessage.setAttribute('tabindex', '-1');
        successMessage.focus();
        
    }, 500);
}

function showErrorMessage(form) {
    // Créer et afficher un message d'erreur générique
    let errorDiv = form.querySelector('.form-general-error');
    
    if (!errorDiv) {
        errorDiv = document.createElement('div');
        errorDiv.className = 'form-general-error';
        errorDiv.style.cssText = `
            background-color: #fee2e2;
            border: 1px solid #fecaca;
            color: #dc2626;
            padding: 1rem;
            border-radius: 0.5rem;
            margin-bottom: 1rem;
            font-size: 0.9rem;
        `;
        form.insertBefore(errorDiv, form.firstChild);
    }
    
    errorDiv.innerHTML = `
        <strong>Erreur lors de l'envoi</strong><br>
        Une erreur s'est produite lors de l'envoi de votre message. 
        Veuillez réessayer ou nous contacter directement par téléphone.
    `;
    
    errorDiv.scrollIntoView({ behavior: 'smooth', block: 'center' });
}

function resetSubmitButton(button, textElement, loaderElement) {
    formSubmitted = false;
    button.disabled = false;
    textElement.style.display = 'inline';
    loaderElement.style.display = 'none';
}

// ===== AMÉLIORATION DE L'EXPÉRIENCE UTILISATEUR =====
function initFormEnhancements() {
    // Auto-complétion intelligente pour l'entreprise
    const companyField = document.getElementById('company');
    if (companyField) {
        // Ici, on pourrait intégrer une API d'auto-complétion d'entreprises
        // ou une base de données locale d'entreprises communes
    }
    
    // Formatage automatique du téléphone
    const phoneField = document.getElementById('phone');
    if (phoneField) {
        phoneField.addEventListener('input', function(e) {
            let value = e.target.value.replace(/\D/g, '');
            if (value.length > 0) {
                if (value.startsWith('33')) {
                    value = '+' + value;
                } else if (value.startsWith('0')) {
                    // Format français standard
                    value = value.replace(/(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})/, '$1 $2 $3 $4 $5');
                }
                e.target.value = value;
            }
        });
    }
    
    // Compteur de caractères pour le message
    const messageField = document.getElementById('message');
    if (messageField) {
        const counter = document.createElement('div');
        counter.className = 'character-counter';
        counter.style.cssText = `
            font-size: 0.8rem;
            color: #6b7280;
            text-align: right;
            margin-top: 0.5rem;
        `;
        messageField.parentNode.appendChild(counter);
        
        function updateCounter() {
            const length = messageField.value.length;
            const minLength = 10;
            const maxLength = 1000;
            
            counter.textContent = `${length}/${maxLength} caractères`;
            
            if (length < minLength) {
                counter.style.color = '#dc2626';
            } else if (length > maxLength * 0.9) {
                counter.style.color = '#f59e0b';
            } else {
                counter.style.color = '#059669';
            }
        }
        
        messageField.addEventListener('input', updateCounter);
        updateCounter();
    }
}

// ===== ANALYTICS ET SUIVI =====
function trackFormInteraction(action, field) {
    if (typeof gtag !== 'undefined') {
        gtag('event', 'form_interaction', {
            event_category: 'Contact Form',
            event_label: field || 'unknown',
            action: action
        });
    }
}

// Tracker les interactions avec les champs du formulaire
document.addEventListener('DOMContentLoaded', function() {
    const formFields = document.querySelectorAll('#contact-form input, #contact-form textarea, #contact-form select');
    
    formFields.forEach(field => {
        field.addEventListener('focus', function() {
            trackFormInteraction('field_focus', this.name);
        });
        
        field.addEventListener('blur', function() {
            if (this.value.trim()) {
                trackFormInteraction('field_complete', this.name);
            }
        });
    });
    
    // Initialiser les améliorations UX
    initFormEnhancements();
});

// ===== GESTION DES ERREURS =====
window.addEventListener('error', function(e) {
    if (e.target.tagName === 'IFRAME' && e.target.src.includes('maps')) {
        console.warn('Erreur de chargement de la carte Google Maps');
        // Masquer la carte ou afficher un message d'erreur alternatif
        const mapContainer = e.target.parentElement;
        if (mapContainer) {
            mapContainer.innerHTML = `
                <div style="
                    background: #f3f4f6; 
                    padding: 2rem; 
                    text-align: center; 
                    border-radius: 0.5rem;
                    color: #6b7280;
                ">
                    <p>La carte n'est pas disponible pour le moment.</p>
                    <p><strong>Adresse :</strong> 123 Avenue des Champs-Élysées, 75008 Paris</p>
                </div>
            `;
        }
    }
});

// ===== EXPORT POUR LES TESTS =====
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        validateField,
        isValidEmail,
        isValidPhone,
        submitForm
    };
}