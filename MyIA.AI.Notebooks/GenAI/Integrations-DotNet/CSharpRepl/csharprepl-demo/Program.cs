// Application de demonstration : un "service de commandes" vivant que le
// notebook va attacher, inspecter et patcher a chaud via CSharpRepl.
//
// Le hook CSharpRepl (DOTNET_STARTUP_HOOKS) est injecte par le notebook ;
// ce programme n'a aucune dependance vers CSharpRepl.

namespace LiveOrderApp;

public static class OrderService
{
    // Compteur d'appels : etat vivant que le notebook lit a chaud via
    // `csharprepl connect <pid> -e "OrderService.ComputeCount"` (sans point-
    // virgule : le REPL imprime le resultat de l'expression).
    public static int ComputeCount;

    // Methode cible du hot-patch : le notebook la remplacera / enveloppera
    // a chaud via `#replace` / `#wrap` sans arreter le process.
    public static decimal CalculatePrice(int quantity, decimal unitPrice)
    {
        ComputeCount++;
        return quantity * unitPrice;
    }
}

public static class Program
{
    public static void Main()
    {
        Console.WriteLine("LiveOrderApp demarre, PID=" + Environment.ProcessId);
        var tick = 0;
        while (true)
        {
            var price = OrderService.CalculatePrice(3, 10m);
            Console.WriteLine($"[{++tick}] price={price}");
            Thread.Sleep(500);
        }
    }
}
