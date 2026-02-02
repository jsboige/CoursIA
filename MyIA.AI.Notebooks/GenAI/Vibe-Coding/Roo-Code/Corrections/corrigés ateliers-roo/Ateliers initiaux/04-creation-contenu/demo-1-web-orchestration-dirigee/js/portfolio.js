// Portfolio functionality
document.addEventListener('DOMContentLoaded', function() {
    // Portfolio filter functionality
    const filterButtons = document.querySelectorAll('.filter-btn');
    const portfolioItems = document.querySelectorAll('.portfolio-item');
    const loadMoreBtn = document.getElementById('loadMore');

    // Initially show only first 6 items
    let visibleItems = 6;
    showItems(visibleItems);

    // Filter button click handlers
    filterButtons.forEach(button => {
        button.addEventListener('click', function() {
            const filter = this.getAttribute('data-filter');
            
            // Update active button
            filterButtons.forEach(btn => btn.classList.remove('active'));
            this.classList.add('active');
            
            // Filter items
            filterPortfolioItems(filter);
            
            // Reset visible items counter
            visibleItems = 6;
            showItems(visibleItems);
        });
    });

    // Load more button functionality
    if (loadMoreBtn) {
        loadMoreBtn.addEventListener('click', function() {
            visibleItems += 3;
            showItems(visibleItems);
            
            // Hide button if all items are visible
            const visiblePortfolioItems = Array.from(portfolioItems).filter(item => 
                item.style.display !== 'none'
            );
            
            if (visibleItems >= visiblePortfolioItems.length) {
                loadMoreBtn.style.display = 'none';
            }
        });
    }

    function filterPortfolioItems(filter) {
        portfolioItems.forEach(item => {
            const categories = item.getAttribute('data-category');
            
            if (filter === 'all' || categories.includes(filter)) {
                item.style.display = 'block';
                item.classList.add('fade-in');
            } else {
                item.style.display = 'none';
                item.classList.remove('fade-in');
            }
        });
    }

    function showItems(count) {
        const visiblePortfolioItems = Array.from(portfolioItems).filter(item => 
            item.style.display !== 'none'
        );
        
        visiblePortfolioItems.forEach((item, index) => {
            if (index < count) {
                item.classList.add('show');
                item.style.opacity = '1';
                item.style.transform = 'translateY(0)';
            } else {
                item.classList.remove('show');
                item.style.opacity = '0';
                item.style.transform = 'translateY(20px)';
            }
        });

        // Show/hide load more button
        if (loadMoreBtn) {
            if (count >= visiblePortfolioItems.length) {
                loadMoreBtn.style.display = 'none';
            } else {
                loadMoreBtn.style.display = 'inline-block';
            }
        }
    }

    // Smooth animations for portfolio items
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('animate-in');
            }
        });
    }, {
        threshold: 0.1,
        rootMargin: '0px 0px -50px 0px'
    });

    portfolioItems.forEach(item => {
        observer.observe(item);
    });

    // Portfolio item hover effects
    portfolioItems.forEach(item => {
        const portfolioLink = item.querySelector('.portfolio-link');
        
        item.addEventListener('mouseenter', function() {
            this.classList.add('hover');
        });
        
        item.addEventListener('mouseleave', function() {
            this.classList.remove('hover');
        });

        // Portfolio link click handler (for demo purposes)
        if (portfolioLink) {
            portfolioLink.addEventListener('click', function(e) {
                e.preventDefault();
                
                const projectTitle = item.querySelector('h3').textContent;
                showProjectModal(projectTitle);
            });
        }
    });

    // Simple modal for project details (demo)
    function showProjectModal(projectTitle) {
        const modal = document.createElement('div');
        modal.className = 'project-modal';
        modal.innerHTML = `
            <div class="modal-content">
                <span class="modal-close">&times;</span>
                <h2>${projectTitle}</h2>
                <p>Détails complets du projet à venir...</p>
                <p>Cette fonctionnalité sera développée dans une future version.</p>
            </div>
        `;
        
        document.body.appendChild(modal);
        
        // Close modal functionality
        const closeBtn = modal.querySelector('.modal-close');
        closeBtn.addEventListener('click', function() {
            document.body.removeChild(modal);
        });
        
        modal.addEventListener('click', function(e) {
            if (e.target === modal) {
                document.body.removeChild(modal);
            }
        });

        // Add modal styles if not exist
        if (!document.querySelector('.modal-styles')) {
            const modalStyles = document.createElement('style');
            modalStyles.className = 'modal-styles';
            modalStyles.textContent = `
                .project-modal {
                    position: fixed;
                    top: 0;
                    left: 0;
                    width: 100%;
                    height: 100%;
                    background: rgba(0, 0, 0, 0.8);
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    z-index: 1000;
                    animation: fadeIn 0.3s ease;
                }
                
                .modal-content {
                    background: white;
                    padding: 2rem;
                    border-radius: 8px;
                    max-width: 500px;
                    width: 90%;
                    position: relative;
                    animation: slideUp 0.3s ease;
                }
                
                .modal-close {
                    position: absolute;
                    top: 1rem;
                    right: 1rem;
                    font-size: 1.5rem;
                    cursor: pointer;
                    color: #666;
                }
                
                .modal-close:hover {
                    color: #000;
                }
                
                @keyframes fadeIn {
                    from { opacity: 0; }
                    to { opacity: 1; }
                }
                
                @keyframes slideUp {
                    from { transform: translateY(50px); opacity: 0; }
                    to { transform: translateY(0); opacity: 1; }
                }
            `;
            document.head.appendChild(modalStyles);
        }
    }
});