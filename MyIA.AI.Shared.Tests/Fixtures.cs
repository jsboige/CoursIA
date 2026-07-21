using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Entities;

namespace MyIA.AI.Shared.Tests;

// Fixtures decorated/marked to prove decoration -> introspection. One fixture per
// combination of the A1 primitives so the tests can assert exact membership.

/// <summary>Flat entity (ISimpleEntity) under the "Payment" main category.</summary>
[MainCategory("Payment")]
public sealed class PaymentGateway : ISimpleEntity
{
    public string Name => "payment-gateway";
}

/// <summary>Hierarchical container under "Content": decorated as AttributeContainer + IChildEntity.</summary>
[MainCategory("Content")]
[AttributeContainer(ChildType = typeof(ContentItem))]
public sealed class ContentFolder : IChildEntity
{
    public IChildEntity? Parent { get; set; }

    private readonly List<IChildEntity> _children = new();

    public IReadOnlyList<IChildEntity> Children => _children;

    public void AddChild(IChildEntity child)
    {
        child.Parent = this;
        _children.Add(child);
    }
}

/// <summary>Hierarchical leaf under "Content": IChildEntity + IMergeable.</summary>
[MainCategory("Content")]
public sealed class ContentItem : IChildEntity, IMergeable
{
    public string Title { get; set; } = string.Empty;

    public IChildEntity? Parent { get; set; }

    public IReadOnlyList<IChildEntity> Children => Array.Empty<IChildEntity>();

    public bool Merge(IMergeable other)
    {
        if (other is ContentItem item)
        {
            if (string.IsNullOrEmpty(Title))
            {
                Title = item.Title;
            }

            return true;
        }

        return false;
    }
}

/// <summary>Undecorated flat entity: appears in SimpleEntities but in NO main category.</summary>
public sealed class PlainLeaf : ISimpleEntity
{
    public string Name => "plain-leaf";
}
