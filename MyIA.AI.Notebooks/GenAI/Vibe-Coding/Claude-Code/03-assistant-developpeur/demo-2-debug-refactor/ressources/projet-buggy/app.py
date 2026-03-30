"""
Application de gestion de tâches avec plusieurs bugs intentionnels.
Utilisez Claude Code pour les identifier et les corriger.
"""

import json
from datetime import datetime

# Bug 1: Variable globale mutable partagée
DEFAULT_TAGS = []

class Task:
    def __init__(self, title, description="", tags=DEFAULT_TAGS):
        self.id = None
        self.title = title
        self.description = description
        self.tags = tags  # Bug 2: Référence partagée
        self.created_at = datetime.now()
        self.completed = False
        self.completed_at = None

    def complete(self):
        self.completed = True
        self.completed_at = datetime.now()

    def add_tag(self, tag):
        self.tags.append(tag)  # Bug 3: Modifie DEFAULT_TAGS

    def to_dict(self):
        return {
            'id': self.id,
            'title': self.title,
            'description': self.description,
            'tags': self.tags,
            'created_at': self.created_at,  # Bug 4: datetime non sérialisable
            'completed': self.completed,
            'completed_at': self.completed_at
        }


class TaskManager:
    def __init__(self):
        self.tasks = []
        self.next_id = 1

    def add_task(self, task):
        task.id = self.next_id
        self.next_id += 1
        self.tasks.append(task)
        return task.id

    def get_task(self, task_id):
        for task in self.tasks:
            if task.id == task_id:
                return task
        return None  # Bug 5: Pas d'exception, silencieux

    def remove_task(self, task_id):
        task = self.get_task(task_id)
        self.tasks.remove(task)  # Bug 6: Crash si task est None

    def get_pending_tasks(self):
        return [t for t in self.tasks if not t.completed]

    def get_completed_tasks(self):
        return [t for t in self.tasks if t.completed]

    def search_tasks(self, keyword):
        results = []
        for task in self.tasks:
            if keyword in task.title or keyword in task.description:
                results.append(task)
        return results

    def get_tasks_by_tag(self, tag):
        # Bug 7: Comparaison case-sensitive
        return [t for t in self.tasks if tag in t.tags]

    def save_to_file(self, filename):
        data = [task.to_dict() for task in self.tasks]
        with open(filename, 'w') as f:
            json.dump(data, f)  # Bug 8: Crash à cause du datetime

    def load_from_file(self, filename):
        with open(filename, 'r') as f:
            data = json.load(f)
        # Bug 9: Pas de gestion si fichier n'existe pas
        # Bug 10: Perd les tâches existantes sans avertissement
        self.tasks = []
        for item in data:
            task = Task(item['title'], item['description'], item['tags'])
            task.completed = item['completed']
            self.tasks.append(task)

    def get_statistics(self):
        total = len(self.tasks)
        completed = len(self.get_completed_tasks())
        pending = len(self.get_pending_tasks())

        # Bug 11: Division par zéro si aucune tâche
        completion_rate = completed / total * 100

        return {
            'total': total,
            'completed': completed,
            'pending': pending,
            'completion_rate': completion_rate
        }


def main():
    manager = TaskManager()

    # Créer des tâches
    task1 = Task("Faire les courses", "Acheter du lait et du pain")
    task1.add_tag("urgent")

    task2 = Task("Réviser Python")
    task2.add_tag("étude")

    manager.add_task(task1)
    manager.add_task(task2)

    # Bug 12: task1.tags contient aussi "étude" à cause du partage
    print(f"Tags de task1: {task1.tags}")
    print(f"Tags de task2: {task2.tags}")

    # Statistiques
    stats = manager.get_statistics()
    print(f"Statistiques: {stats}")

    # Sauvegarder
    manager.save_to_file("tasks.json")


if __name__ == "__main__":
    main()
