// Copyright (c) Microsoft. All rights reserved.

using System.Drawing;
using Microsoft.DotNet.Interactive;
using SkiaSharp;

// ReSharper disable InconsistentNaming
namespace MyIA.AI.Notebooks.Config;

public static class SkiaUtils
{
	// Function used to display images in the notebook
	public static async Task<DisplayedValue> ShowImage(string path, int width, int height, DisplayedValue placeholder = null)
	{
		SKImageInfo info = new SKImageInfo(width, height);
		using (var surface = SKSurface.Create(info))
		{
			var canvas = surface.Canvas;
			canvas.Clear(SKColors.White);

			if (File.Exists(path)) // Vérifier si le chemin est un fichier local
			{
				using (var stream = File.OpenRead(path))
				{
					using (var bitmap = SKBitmap.Decode(stream))
					{
						canvas.DrawBitmap(bitmap, 0, 0);
					}
				}
			}
			else // Sinon, traiter comme une URL distante
			{
				using (var httpClient = new HttpClient())
				{
					using (Stream stream = await httpClient.GetStreamAsync(path))
					using (var bitmap = SKBitmap.Decode(stream))
					{
						canvas.DrawBitmap(bitmap, 0, 0);
					}
				}
			}

			// Capture l'image en tant que SKImage
			var skImage = surface.Snapshot();

			// Si un placeholder est fourni, mettez-le à jour
			if (placeholder != null)
			{
				placeholder.Update(ToBitmap(skImage));
				return placeholder;
			}

			// Sinon, créez et retournez un nouvel objet DisplayedValue
			return skImage.Display();
		}
	}


	public static Bitmap ToBitmap(SKImage skImage)
	{
		using (var data = skImage.Encode(SKEncodedImageFormat.Png, 100))
		using (var stream = new MemoryStream())
		{
			data.SaveTo(stream);
			stream.Seek(0, SeekOrigin.Begin);
			return new Bitmap(stream);
		}
	}


}